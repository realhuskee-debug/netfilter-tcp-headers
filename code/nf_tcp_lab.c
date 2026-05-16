#include <linux/init.h>
#include <linux/module.h>
#include <linux/kernel.h>
#include <linux/version.h>

#include <linux/netfilter.h>
#include <linux/netfilter_ipv4.h>

#include <linux/ip.h>
#include <linux/tcp.h>
#include <linux/skbuff.h>

#include <linux/inet.h>
#include <linux/spinlock.h>
#include <linux/ktime.h>

#include <linux/proc_fs.h>
#include <linux/seq_file.h>
#include <linux/uaccess.h>

MODULE_LICENSE("GPL");
MODULE_AUTHOR("Research Lab");
MODULE_DESCRIPTION("Laboratory Netfilter TCP observer with procfs statistics");
MODULE_VERSION("1.1");

static char *target_saddr = "";
module_param(target_saddr, charp, 0644);
MODULE_PARM_DESC(target_saddr, "Optional source IPv4 filter");

static char *target_daddr = "";
module_param(target_daddr, charp, 0644);
MODULE_PARM_DESC(target_daddr, "Optional destination IPv4 filter");

static unsigned short target_sport = 0;
module_param(target_sport, ushort, 0644);
MODULE_PARM_DESC(target_sport, "Optional source TCP port filter");

static unsigned short target_dport = 0;
module_param(target_dport, ushort, 0644);
MODULE_PARM_DESC(target_dport, "Optional destination TCP port filter");

static bool enable_transform = false;
module_param(enable_transform, bool, 0644);
MODULE_PARM_DESC(enable_transform, "Enable transform path stub");

static unsigned int transform_level = 4;
module_param(transform_level, uint, 0644);
MODULE_PARM_DESC(transform_level, "Transform intensity level: 4, 8, 12");

static char *proc_name = "nf_tcp_lab_stats";
module_param(proc_name, charp, 0444);
MODULE_PARM_DESC(proc_name, "procfs statistics file name");

struct nf_hook_ops nfho;
static struct proc_dir_entry *proc_entry;

struct lab_stats {
        u64 total_packets;
        u64 total_tcp_packets;
        u64 total_tcp_payload_bytes;
        u64 total_ip_bytes;

        u64 syn_packets;
        u64 ack_packets;
        u64 fin_packets;
        u64 rst_packets;
        u64 psh_packets;

        u64 filtered_packets;
        u64 malformed_packets;
        u64 non_linear_packets;
        u64 transform_calls;
        u64 transform_errors;

        u64 hook_time_ns_total;
        u64 hook_time_ns_max;
};

static struct lab_stats stats;
static DEFINE_SPINLOCK(stats_lock);

static __be32 filter_saddr;
static __be32 filter_daddr;

static inline bool addr_match(__be32 pkt_addr, __be32 filter_addr)
{
        if (filter_addr == 0)
                return true;
        return pkt_addr == filter_addr;
}

static inline bool port_match(__be16 pkt_port, unsigned short filter_port)
{
        if (filter_port == 0)
                return true;
        return ntohs(pkt_port) == filter_port;
}

static void stats_inc_simple(u64 *field)
{
        unsigned long flags;

        spin_lock_irqsave(&stats_lock, flags);
        (*field)++;
        spin_unlock_irqrestore(&stats_lock, flags);
}

static void stats_add_packet(const struct iphdr *iph, const struct tcphdr *tcph,
                             unsigned int payload_len, u64 hook_delta_ns)
{
        unsigned long flags;

        spin_lock_irqsave(&stats_lock, flags);

        stats.total_tcp_packets++;
        stats.total_ip_bytes += ntohs(iph->tot_len);
        stats.total_tcp_payload_bytes += payload_len;

        if (tcph->syn)
                stats.syn_packets++;
        if (tcph->ack)
                stats.ack_packets++;
        if (tcph->fin)
                stats.fin_packets++;
        if (tcph->rst)
                stats.rst_packets++;
        if (tcph->psh)
                stats.psh_packets++;

        stats.hook_time_ns_total += hook_delta_ns;
        if (hook_delta_ns > stats.hook_time_ns_max)
                stats.hook_time_ns_max = hook_delta_ns;

        spin_unlock_irqrestore(&stats_lock, flags);
}

static int transform_stub(struct sk_buff *skb, struct iphdr *iph, struct tcphdr *tcph)
{
        unsigned long flags;
        unsigned int ip_hdr_len;
        unsigned int tcp_hdr_len;
        unsigned int opt_len;
        unsigned int copy_len;
        unsigned int rounds;
        unsigned int i;
        u32 acc = 0;
        unsigned char tmp[64];
        unsigned char *tcp_ptr;

        spin_lock_irqsave(&stats_lock, flags);
        stats.transform_calls++;
        spin_unlock_irqrestore(&stats_lock, flags);

        if (!skb || !iph || !tcph)
                return -EINVAL;

        ip_hdr_len = iph->ihl * 4;
        tcp_hdr_len = tcph->doff * 4;

        if (ip_hdr_len < sizeof(struct iphdr))
                return -EINVAL;

        if (tcp_hdr_len < sizeof(struct tcphdr))
                return -EINVAL;

        if (!pskb_may_pull(skb, ip_hdr_len + tcp_hdr_len))
                return -EINVAL;

        iph = ip_hdr(skb);
        if (!iph)
                return -EINVAL;

        tcp_ptr = (unsigned char *)iph + ip_hdr_len;
        tcph = (struct tcphdr *)tcp_ptr;

        tcp_hdr_len = tcph->doff * 4;
        if (tcp_hdr_len < sizeof(struct tcphdr))
                return -EINVAL;

        opt_len = tcp_hdr_len - sizeof(struct tcphdr);

        copy_len = tcp_hdr_len;
        if (copy_len > sizeof(tmp))
                copy_len = sizeof(tmp);

        memcpy(tmp, tcp_ptr, copy_len);

        for (i = 0; i < copy_len; i++)
                acc = (acc * 33u) ^ tmp[i];

        if (opt_len > 0) {
                for (i = sizeof(struct tcphdr); i < copy_len; i++)
                        acc ^= ((u32)tmp[i] << (i & 7));
        }

        switch (transform_level) {
        case 4:
                rounds = 256;
                break;
        case 8:
                rounds = 1024;
                break;
        case 12:
                rounds = 4096;
                break;
        default:
                rounds = 256 * transform_level;
                if (rounds < 256)
                        rounds = 256;
                if (rounds > 20000)
                        rounds = 20000;
                break;
        }

        for (i = 0; i < rounds; i++) {
                acc = (acc * 1103515245u + 12345u) & 0x7fffffffu;
                acc ^= (acc >> 7);
                acc ^= (acc << 9);
        }

        if (unlikely(acc == 0x12345678u))
                return 1;

        return 0;
}

static unsigned int nf_tcp_lab_hook(void *priv, struct sk_buff *skb,
                                    const struct nf_hook_state *state)
{
        struct iphdr *iph;
        struct tcphdr *tcph;
        unsigned int ip_hdr_len;
        unsigned int tcp_hdr_len;
        unsigned int total_len;
        unsigned int payload_len;
        ktime_t t0, t1;
        u64 delta_ns;

        (void)priv;
        (void)state;

        if (!skb)
                return NF_ACCEPT;

        t0 = ktime_get();

        stats_inc_simple(&stats.total_packets);

        if (!pskb_may_pull(skb, sizeof(struct iphdr)))
                return NF_ACCEPT;

        iph = ip_hdr(skb);
        if (!iph) {
                stats_inc_simple(&stats.malformed_packets);
                return NF_ACCEPT;
        }

        if (iph->version != 4 || iph->protocol != IPPROTO_TCP)
                return NF_ACCEPT;

        if (!addr_match(iph->saddr, filter_saddr) || !addr_match(iph->daddr, filter_daddr)) {
                stats_inc_simple(&stats.filtered_packets);
                return NF_ACCEPT;
        }

        ip_hdr_len = iph->ihl * 4;
        if (ip_hdr_len < sizeof(struct iphdr)) {
                stats_inc_simple(&stats.malformed_packets);
                return NF_ACCEPT;
        }

        if (!pskb_may_pull(skb, ip_hdr_len + sizeof(struct tcphdr))) {
                stats_inc_simple(&stats.malformed_packets);
                return NF_ACCEPT;
        }

        iph = ip_hdr(skb);
        tcph = (struct tcphdr *)((unsigned char *)iph + ip_hdr_len);

        if (!port_match(tcph->source, target_sport) || !port_match(tcph->dest, target_dport)) {
                stats_inc_simple(&stats.filtered_packets);
                return NF_ACCEPT;
        }

        tcp_hdr_len = tcph->doff * 4;
        if (tcp_hdr_len < sizeof(struct tcphdr)) {
                stats_inc_simple(&stats.malformed_packets);
                return NF_ACCEPT;
        }

        total_len = ntohs(iph->tot_len);
        if (total_len < ip_hdr_len + tcp_hdr_len) {
                stats_inc_simple(&stats.malformed_packets);
                return NF_ACCEPT;
        }

        payload_len = total_len - ip_hdr_len - tcp_hdr_len;

        if (skb_is_nonlinear(skb))
                stats_inc_simple(&stats.non_linear_packets);

        if (enable_transform) {
                if (transform_stub(skb, iph, tcph) != 0)
                        stats_inc_simple(&stats.transform_errors);
        }

        t1 = ktime_get();
        delta_ns = ktime_to_ns(ktime_sub(t1, t0));

        stats_add_packet(iph, tcph, payload_len, delta_ns);

        return NF_ACCEPT;
}

static int nf_tcp_lab_proc_show(struct seq_file *m, void *v)
{
        unsigned long flags;
        u64 avg_ns = 0;

        (void)v;

        spin_lock_irqsave(&stats_lock, flags);

        if (stats.total_tcp_packets != 0)
                avg_ns = div64_u64(stats.hook_time_ns_total, stats.total_tcp_packets);

        seq_printf(m, "module=nf_tcp_lab\n");
        seq_printf(m, "enable_transform=%u\n", enable_transform ? 1 : 0);
        seq_printf(m, "transform_level=%u\n", transform_level);
        seq_printf(m, "target_saddr=%s\n", target_saddr[0] ? target_saddr : "any");
        seq_printf(m, "target_daddr=%s\n", target_daddr[0] ? target_daddr : "any");
        seq_printf(m, "target_sport=%u\n", target_sport);
        seq_printf(m, "target_dport=%u\n", target_dport);

        seq_printf(m, "total_packets=%llu\n", stats.total_packets);
        seq_printf(m, "total_tcp_packets=%llu\n", stats.total_tcp_packets);
        seq_printf(m, "total_ip_bytes=%llu\n", stats.total_ip_bytes);
        seq_printf(m, "total_tcp_payload_bytes=%llu\n", stats.total_tcp_payload_bytes);

        seq_printf(m, "syn_packets=%llu\n", stats.syn_packets);
        seq_printf(m, "ack_packets=%llu\n", stats.ack_packets);
        seq_printf(m, "fin_packets=%llu\n", stats.fin_packets);
        seq_printf(m, "rst_packets=%llu\n", stats.rst_packets);
        seq_printf(m, "psh_packets=%llu\n", stats.psh_packets);

        seq_printf(m, "filtered_packets=%llu\n", stats.filtered_packets);
        seq_printf(m, "malformed_packets=%llu\n", stats.malformed_packets);
        seq_printf(m, "non_linear_packets=%llu\n", stats.non_linear_packets);

        seq_printf(m, "transform_calls=%llu\n", stats.transform_calls);
        seq_printf(m, "transform_errors=%llu\n", stats.transform_errors);

        seq_printf(m, "hook_time_ns_total=%llu\n", stats.hook_time_ns_total);
        seq_printf(m, "hook_time_ns_avg=%llu\n", avg_ns);
        seq_printf(m, "hook_time_ns_max=%llu\n", stats.hook_time_ns_max);

        spin_unlock_irqrestore(&stats_lock, flags);

        return 0;
}

static int nf_tcp_lab_proc_open(struct inode *inode, struct file *file)
{
        return single_open(file, nf_tcp_lab_proc_show, NULL);
}

#if LINUX_VERSION_CODE >= KERNEL_VERSION(5, 6, 0)
static const struct proc_ops nf_tcp_lab_proc_ops = {
        .proc_open    = nf_tcp_lab_proc_open,
        .proc_read    = seq_read,
        .proc_lseek   = seq_lseek,
        .proc_release = single_release,
};
#else
static const struct file_operations nf_tcp_lab_proc_ops = {
        .owner   = THIS_MODULE,
        .open    = nf_tcp_lab_proc_open,
        .read    = seq_read,
        .llseek  = seq_lseek,
        .release = single_release,
};
#endif

static int __init nf_tcp_lab_init(void)
{
        int ret;

        memset(&stats, 0, sizeof(stats));
        filter_saddr = 0;
        filter_daddr = 0;

        if (target_saddr[0]) {
                ret = in4_pton(target_saddr, -1, (u8 *)&filter_saddr, -1, NULL);
                if (!ret) {
                        pr_err("nf_tcp_lab: invalid target_saddr\n");
                        return -EINVAL;
                }
        }

        if (target_daddr[0]) {
                ret = in4_pton(target_daddr, -1, (u8 *)&filter_daddr, -1, NULL);
                if (!ret) {
                        pr_err("nf_tcp_lab: invalid target_daddr\n");
                        return -EINVAL;
                }
        }

        nfho.hook = nf_tcp_lab_hook;
        nfho.pf = NFPROTO_IPV4;
        nfho.hooknum = NF_INET_POST_ROUTING;
        nfho.priority = NF_IP_PRI_FIRST;

        ret = nf_register_net_hook(&init_net, &nfho);
        if (ret) {
                pr_err("nf_tcp_lab: nf_register_net_hook failed: %d\n", ret);
                return ret;
        }

        proc_entry = proc_create(proc_name, 0444, NULL, &nf_tcp_lab_proc_ops);
        if (!proc_entry) {
                nf_unregister_net_hook(&init_net, &nfho);
                pr_err("nf_tcp_lab: proc_create failed\n");
                return -ENOMEM;
        }

        pr_info("nf_tcp_lab: loaded\n");
        return 0;
}

static void __exit nf_tcp_lab_exit(void)
{
        remove_proc_entry(proc_name, NULL);
        nf_unregister_net_hook(&init_net, &nfho);

        pr_info("nf_tcp_lab: unloaded total_packets=%llu total_tcp_packets=%llu total_payload=%llu\n",
                stats.total_packets, stats.total_tcp_packets, stats.total_tcp_payload_bytes);
}

module_init(nf_tcp_lab_init);
module_exit(nf_tcp_lab_exit);
