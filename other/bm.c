#define TS_IGNORECASE 2

#define UINT_MAX (~0U)

#define max_t(type,x,y) ({ type __max1 = (x); type __max2 = (y); __max1 > __max2 ? __max1: __max2; })

#define unlikely(x) __builtin_expect(!!(x), 0)

#define tolower(c) __tolower(c)

#define toupper(c) __toupper(c)

#define DEBUGP(a,...)

enum {
 SB_UNFROZEN = 0,
 SB_FREEZE_WRITE = 1,
 SB_FREEZE_PAGEFAULT = 2,
 SB_FREEZE_FS = 3,
 SB_FREEZE_COMPLETE = 4,
};

enum {
 MM_FILEPAGES,
 MM_ANONPAGES,
 MM_SWAPENTS,
 NR_MM_COUNTERS
};

enum kobj_ns_type {
 KOBJ_NS_TYPE_NONE = 0,
 KOBJ_NS_TYPE_NET,
 KOBJ_NS_TYPES
};

enum migrate_mode {
 MIGRATE_ASYNC,
 MIGRATE_SYNC_LIGHT,
 MIGRATE_SYNC,
};

enum module_state {
 MODULE_STATE_LIVE,
 MODULE_STATE_COMING,
 MODULE_STATE_GOING,
 MODULE_STATE_UNFORMED,
};

enum pid_type
{
 PIDTYPE_PID,
 PIDTYPE_PGID,
 PIDTYPE_SID,
 PIDTYPE_MAX
};

enum quota_type {
 USRQUOTA = 0,
 GRPQUOTA = 1,
 PRJQUOTA = 2,
};

typedef unsigned int __kernel_gid32_t;

typedef long long __kernel_loff_t;

typedef long __kernel_long_t;

typedef unsigned int __kernel_uid32_t;

typedef unsigned long __kernel_ulong_t;

typedef unsigned short __u16;

typedef unsigned int __u32;

typedef unsigned long long __u64;

typedef struct {
 long counter;
} atomic64_t;

typedef struct {
 int counter;
} atomic_t;

typedef unsigned long blkcnt_t;

typedef _Bool bool;

typedef void compound_page_dtor(struct page *);

typedef struct cpumask { unsigned long bits[(((64) + (8 * sizeof(long)) - 1) / (8 * sizeof(long)))]; } cpumask_t;

typedef void *fl_owner_t;

typedef unsigned fmode_t;

typedef unsigned gfp_t;

typedef unsigned long pgdval_t;

typedef unsigned long pgprotval_t;

typedef long long qsize_t;

typedef signed int s32;

typedef signed long long s64;

typedef signed char s8;

typedef unsigned long sector_t;

typedef struct seqcount {
 unsigned sequence;
} seqcount_t;

typedef unsigned short u16;

typedef unsigned int u32;

typedef unsigned long long u64;

typedef unsigned char u8;

typedef unsigned short umode_t;

struct bug_entry {
 signed int bug_addr_disp;
 signed int file_disp;
 unsigned short line;
 unsigned short flags;
};

struct callback_head {
 struct callback_head *next;
 void (*func)(struct callback_head *head);
};

struct core_thread {
 struct task_struct *task;
 struct core_thread *next;
};

struct file_lock_operations {
 void (*fl_copy_lock)(struct file_lock *, struct file_lock *);
 void (*fl_release_private)(struct file_lock *);
};

struct hlist_bl_node {
 struct hlist_bl_node *next, **pprev;
};

struct hlist_node {
 struct hlist_node *next, **pprev;
};

struct ida_bitmap {
 long nr_busy;
 unsigned long bitmap[(128 / sizeof(long) - 1)];
};

struct kernel_param_ops {
 unsigned int flags;
 int (*set)(const char *val, const struct kernel_param *kp);
 int (*get)(char *buffer, const struct kernel_param *kp);
 void (*free)(void *arg);
};

struct kernel_symbol
{
 unsigned long value;
 const char *name;
};

struct kernfs_elem_symlink {
 struct kernfs_node *target_kn;
};

struct kparam_string {
 unsigned int maxlen;
 char *string;
};

struct kset_uevent_ops {
 int (* const filter)(struct kset *kset, struct kobject *kobj);
 const char *(* const name)(struct kset *kset, struct kobject *kobj);
 int (* const uevent)(struct kset *kset, struct kobject *kobj,
        struct kobj_uevent_env *env);
};

struct list_head {
 struct list_head *next, *prev;
};

struct llist_node {
 struct llist_node *next;
};

struct lock_class_key { };

struct mod_arch_specific
{
};

struct nfs4_lock_info {
 struct nfs4_lock_state *owner;
};

struct path {
 struct vfsmount *mnt;
 struct dentry *dentry;
};

struct qc_info {
 int i_fieldmask;
 unsigned int i_flags;
 unsigned int i_spc_timelimit;
 unsigned int i_ino_timelimit;
 unsigned int i_rt_spc_timelimit;
 unsigned int i_spc_warnlimit;
 unsigned int i_ino_warnlimit;
 unsigned int i_rt_spc_warnlimit;
};

struct rb_node {
 unsigned long __rb_parent_color;
 struct rb_node *rb_right;
 struct rb_node *rb_left;
};

struct ts_state
{
 unsigned int offset;
 char cb[40];
};

struct uprobes_state {
};

typedef __u64 Elf64_Addr;

typedef __u16 Elf64_Half;

typedef __u32 Elf64_Word;

typedef __u64 Elf64_Xword;

typedef __u32 __kernel_dev_t;

typedef __kernel_ulong_t __kernel_size_t;

typedef __kernel_long_t __kernel_ssize_t;

typedef __kernel_long_t __kernel_time_t;

typedef struct qspinlock {
 atomic_t val;
} arch_spinlock_t;

typedef atomic64_t atomic_long_t;

typedef struct cpumask cpumask_var_t[1];

typedef __kernel_gid32_t gid_t;

typedef __kernel_loff_t loff_t;

typedef struct { pgdval_t pgd; } pgd_t;

typedef struct pgprot { pgprotval_t pgprot; } pgprot_t;

typedef __kernel_uid32_t projid_t;

typedef __kernel_uid32_t uid_t;

struct attribute {
 const char *name;
 umode_t mode;
};

struct fiemap_extent {
 __u64 fe_logical;
 __u64 fe_physical;
 __u64 fe_length;
 __u64 fe_reserved64[2];
 __u32 fe_flags;
 __u32 fe_reserved[3];
};

struct hlist_bl_head {
 struct hlist_bl_node *first;
};

struct hlist_head {
 struct hlist_node *first;
};

struct idr_layer {
 int prefix;
 int layer;
 struct idr_layer *ary[1<<8];
 int count;
 union {
  unsigned long bitmap[((((1 << 8)) + (8 * sizeof(long)) - 1) / (8 * sizeof(long)))];
  struct callback_head callback_head;
 };
};

struct kobj_ns_type_operations {
 enum kobj_ns_type type;
 bool (*current_may_mount)(void);
 void *(*grab_current_ns)(void);
 const void *(*netlink_ns)(struct sock *sk);
 const void *(*initial_ns)(void);
 void (*drop_ns)(void *);
};

struct kparam_array
{
 unsigned int max;
 unsigned int elemsize;
 unsigned int *num;
 const struct kernel_param_ops *ops;
 void *elem;
};

struct kref {
 atomic_t refcount;
};

struct latch_tree_node {
 struct rb_node node[2];
};

struct list_lru_one {
 struct list_head list;
 long nr_items;
};

struct lock_manager_operations {
 int (*lm_compare_owner)(struct file_lock *, struct file_lock *);
 unsigned long (*lm_owner_key)(struct file_lock *);
 fl_owner_t (*lm_get_owner)(fl_owner_t);
 void (*lm_put_owner)(fl_owner_t);
 void (*lm_notify)(struct file_lock *);
 int (*lm_grant)(struct file_lock *, int);
 bool (*lm_break)(struct file_lock *);
 int (*lm_change)(struct file_lock *, int, struct list_head *);
 void (*lm_setup)(struct file_lock *, void **);
};

struct nfs_lock_info {
 u32 state;
 struct nlm_lockowner *owner;
 struct list_head list;
};

struct optimistic_spin_queue {
 atomic_t tail;
};

struct qc_dqblk {
 int d_fieldmask;
 u64 d_spc_hardlimit;
 u64 d_spc_softlimit;
 u64 d_ino_hardlimit;
 u64 d_ino_softlimit;
 u64 d_space;
 u64 d_ino_count;
 s64 d_ino_timer;
 s64 d_spc_timer;
 int d_ino_warns;
 int d_spc_warns;
 u64 d_rt_spc_hardlimit;
 u64 d_rt_spc_softlimit;
 u64 d_rt_space;
 s64 d_rt_spc_timer;
 int d_rt_spc_warns;
};

struct qc_type_state {
 unsigned int flags;
 unsigned int spc_timelimit;
 unsigned int ino_timelimit;
 unsigned int rt_spc_timelimit;
 unsigned int spc_warnlimit;
 unsigned int ino_warnlimit;
 unsigned int rt_spc_warnlimit;
 unsigned long long ino;
 blkcnt_t blocks;
 blkcnt_t nextents;
};

struct qstr {
 union {
  struct {
   u32 hash; u32 len;;
  };
  u64 hash_len;
 };
 const unsigned char *name;
};

struct radix_tree_node {
 unsigned int path;
 unsigned int count;
 union {
  struct {
   struct radix_tree_node *parent;
   void *private_data;
  };
  struct callback_head callback_head;
 };
 struct list_head private_list;
 void *slots[(1UL << (0 ? 4 : 6))];
 unsigned long tags[3][(((1UL << (0 ? 4 : 6)) + 64 - 1) / 64)];
};

struct rb_root {
 struct rb_node *rb_node;
};

struct shrink_control {
 gfp_t gfp_mask;
 unsigned long nr_to_scan;
 int nid;
 struct mem_cgroup *memcg;
};

struct ts_config
{
 struct ts_ops *ops;
 int flags;
 unsigned int (*get_next_block)(unsigned int consumed,
        const u8 **dst,
        struct ts_config *conf,
        struct ts_state *state);
 void (*finish)(struct ts_config *conf,
       struct ts_state *state);
};

struct upid {
 int nr;
 struct pid_namespace *ns;
 struct hlist_node pid_chain;
};

typedef struct elf64_sym {
  Elf64_Word st_name;
  unsigned char st_info;
  unsigned char st_other;
  Elf64_Half st_shndx;
  Elf64_Addr st_value;
  Elf64_Xword st_size;
} Elf64_Sym;

typedef struct qrwlock {
 atomic_t cnts;
 arch_spinlock_t lock;
} arch_rwlock_t;

typedef __kernel_dev_t dev_t;

typedef int (*filldir_t)(struct dir_context *, const char *, int, loff_t, u64,
    unsigned);

typedef struct {
 gid_t val;
} kgid_t;

typedef struct {
 projid_t val;
} kprojid_t;

typedef struct {
 uid_t val;
} kuid_t;

typedef struct raw_spinlock {
 arch_spinlock_t raw_lock;
} raw_spinlock_t;

typedef __kernel_size_t size_t;

typedef __kernel_ssize_t ssize_t;

typedef __kernel_time_t time_t;

struct dentry_operations {
 int (*d_revalidate)(struct dentry *, unsigned int);
 int (*d_weak_revalidate)(struct dentry *, unsigned int);
 int (*d_hash)(const struct dentry *, struct qstr *);
 int (*d_compare)(const struct dentry *, const struct dentry *,
   unsigned int, const char *, const struct qstr *);
 int (*d_delete)(const struct dentry *);
 void (*d_release)(struct dentry *);
 void (*d_prune)(struct dentry *);
 void (*d_iput)(struct dentry *, struct inode *);
 char *(*d_dname)(struct dentry *, char *, int);
 struct vfsmount *(*d_automount)(struct path *);
 int (*d_manage)(struct dentry *, bool);
 struct inode *(*d_select_inode)(struct dentry *, unsigned);
};

struct fiemap_extent_info {
 unsigned int fi_flags;
 unsigned int fi_extents_mapped;
 unsigned int fi_extents_max;
 struct fiemap_extent *fi_extents_start;
};

struct file_ra_state {
 unsigned long start;
 unsigned int size;
 unsigned int async_size;
 unsigned int ra_pages;
 unsigned int mmap_miss;
 loff_t prev_pos;
};

struct kernel_param {
 const char *name;
 struct module *mod;
 const struct kernel_param_ops *ops;
 const u16 perm;
 s8 level;
 u8 flags;
 union {
  void *arg;
  const struct kparam_string *str;
  const struct kparam_array *arr;
 };
};

struct kernfs_elem_attr {
 const struct kernfs_ops *ops;
 struct kernfs_open_node *open;
 loff_t size;
 struct kernfs_node *notify_next;
};

struct kernfs_elem_dir {
 unsigned long subdirs;
 struct rb_root children;
 struct kernfs_root *root;
};

struct mm_rss_stat {
 atomic_long_t count[NR_MM_COUNTERS];
};

struct mod_tree_node {
 struct module *mod;
 struct latch_tree_node node;
};

struct pid
{
 atomic_t count;
 unsigned int level;
 struct hlist_head tasks[PIDTYPE_MAX];
 struct callback_head rcu;
 struct upid numbers[1];
};

struct qc_state {
 unsigned int s_incoredqs;
 struct qc_type_state s_state[3];
};

struct radix_tree_root {
 unsigned int height;
 gfp_t gfp_mask;
 struct radix_tree_node *rnode;
};

struct shrinker {
 unsigned long (*count_objects)(struct shrinker *,
           struct shrink_control *sc);
 unsigned long (*scan_objects)(struct shrinker *,
          struct shrink_control *sc);
 int seeks;
 long batch;
 unsigned long flags;
 struct list_head list;
 atomic_long_t *nr_deferred;
};

struct timespec {
 __kernel_time_t tv_sec;
 long tv_nsec;
};

typedef struct {
 arch_rwlock_t raw_lock;
} rwlock_t;

typedef struct spinlock {
 union {
  struct raw_spinlock rlock;
 };
} spinlock_t;

struct dir_context {
 const filldir_t actor;
 loff_t pos;
};

struct kernfs_node {
 atomic_t count;
 atomic_t active;
 struct kernfs_node *parent;
 const char *name;
 struct rb_node rb;
 const void *ns;
 unsigned int hash;
 union {
  struct kernfs_elem_dir dir;
  struct kernfs_elem_symlink symlink;
  struct kernfs_elem_attr attr;
 };
 void *priv;
 unsigned short flags;
 umode_t mode;
 unsigned int ino;
 struct kernfs_iattrs *iattr;
};

struct kqid {
 union {
  kuid_t uid;
  kgid_t gid;
  kprojid_t projid;
 };
 enum quota_type type;
};

struct kstat {
 u64 ino;
 dev_t dev;
 umode_t mode;
 unsigned int nlink;
 kuid_t uid;
 kgid_t gid;
 dev_t rdev;
 loff_t size;
 struct timespec atime;
 struct timespec mtime;
 struct timespec ctime;
 unsigned long blksize;
 unsigned long long blocks;
};

struct mem_dqblk {
 qsize_t dqb_bhardlimit;
 qsize_t dqb_bsoftlimit;
 qsize_t dqb_curspace;
 qsize_t dqb_rsvspace;
 qsize_t dqb_ihardlimit;
 qsize_t dqb_isoftlimit;
 qsize_t dqb_curinodes;
 time_t dqb_btime;
 time_t dqb_itime;
};

struct percpu_counter {
 raw_spinlock_t lock;
 s64 count;
 struct list_head list;
 s32 *counters;
};

struct rw_semaphore {
 long count;
 struct list_head wait_list;
 raw_spinlock_t wait_lock;
 struct optimistic_spin_queue osq;
 struct task_struct *owner;
};

struct __wait_queue_head {
 spinlock_t lock;
 struct list_head task_list;
};

struct file_lock_context {
 spinlock_t flc_lock;
 struct list_head flc_flock;
 struct list_head flc_posix;
 struct list_head flc_lease;
};

struct fown_struct {
 rwlock_t lock;
 struct pid *pid;
 enum pid_type pid_type;
 kuid_t uid, euid;
 int signum;
};

struct idr {
 struct idr_layer *hint;
 struct idr_layer *top;
 int layers;
 int cur;
 spinlock_t lock;
 int id_free_cnt;
 struct idr_layer *id_free;
};

struct kernfs_syscall_ops {
 int (*remount_fs)(struct kernfs_root *root, int *flags, char *data);
 int (*show_options)(struct seq_file *sf, struct kernfs_root *root);
 int (*mkdir)(struct kernfs_node *parent, const char *name,
       umode_t mode);
 int (*rmdir)(struct kernfs_node *kn);
 int (*rename)(struct kernfs_node *kn, struct kernfs_node *new_parent,
        const char *new_name);
};

struct kobject {
 const char *name;
 struct list_head entry;
 struct kobject *parent;
 struct kset *kset;
 struct kobj_type *ktype;
 struct kernfs_node *sd;
 struct kref kref;
 unsigned int state_initialized:1;
 unsigned int state_in_sysfs:1;
 unsigned int state_add_uevent_sent:1;
 unsigned int state_remove_uevent_sent:1;
 unsigned int uevent_suppress:1;
};

struct list_lru_node {
 spinlock_t lock;
 struct list_lru_one lru;
};

struct lockref {
 union {
  __u64  lock_count;
  struct {
   spinlock_t lock;
   atomic_t count;
  };
 };
};

struct mutex {
 atomic_t count;
 spinlock_t wait_lock;
 struct list_head wait_list;
 struct task_struct *owner;
 struct optimistic_spin_queue osq;
};

struct page {
 unsigned long flags;
 union {
  struct address_space *mapping;
  void *s_mem;
 };
 struct {
  union {
   unsigned long index;
   void *freelist;
  };
  union {
   unsigned long counters;
   struct {
    union {
     atomic_t _mapcount;
     struct {
      unsigned inuse:16;
      unsigned objects:15;
      unsigned frozen:1;
     };
     int units;
    };
    atomic_t _count;
   };
   unsigned int active;
  };
 };
 union {
  struct list_head lru;
  struct {
   struct page *next;
   int pages;
   int pobjects;
  };
  struct slab *slab_page;
  struct callback_head callback_head;
  struct {
   compound_page_dtor *compound_dtor;
   unsigned long compound_order;
  };
 };
 union {
  unsigned long private;
  spinlock_t ptl;
  struct kmem_cache *slab_cache;
  struct page *first_page;
 };
};

struct quotactl_ops {
 int (*quota_on)(struct super_block *, int, int, struct path *);
 int (*quota_off)(struct super_block *, int);
 int (*quota_enable)(struct super_block *, unsigned int);
 int (*quota_disable)(struct super_block *, unsigned int);
 int (*quota_sync)(struct super_block *, int);
 int (*set_info)(struct super_block *, int, struct qc_info *);
 int (*get_dqblk)(struct super_block *, struct kqid, struct qc_dqblk *);
 int (*set_dqblk)(struct super_block *, struct kqid, struct qc_dqblk *);
 int (*get_state)(struct super_block *, struct qc_state *);
 int (*rm_xquota)(struct super_block *, unsigned int);
};

typedef struct {
 struct ldt_struct *ldt;
 unsigned short ia32_compat;
 struct mutex lock;
 unsigned long vdso;
 atomic_t perf_rdpmc_allowed;
} mm_context_t;

typedef struct __wait_queue_head wait_queue_head_t;

struct block_device {
 dev_t bd_dev;
 int bd_openers;
 struct inode * bd_inode;
 struct super_block * bd_super;
 struct mutex bd_mutex;
 struct list_head bd_inodes;
 void * bd_claiming;
 void * bd_holder;
 int bd_holders;
 bool bd_write_holder;
 struct list_head bd_holder_disks;
 struct block_device * bd_contains;
 unsigned bd_block_size;
 struct hd_struct * bd_part;
 unsigned bd_part_count;
 int bd_invalidated;
 struct gendisk * bd_disk;
 struct request_queue * bd_queue;
 struct list_head bd_list;
 unsigned long bd_private;
 int bd_fsfreeze_count;
 struct mutex bd_fsfreeze_mutex;
};

struct dentry {
 unsigned int d_flags;
 seqcount_t d_seq;
 struct hlist_bl_node d_hash;
 struct dentry *d_parent;
 struct qstr d_name;
 struct inode *d_inode;
 unsigned char d_iname[32];
 struct lockref d_lockref;
 const struct dentry_operations *d_op;
 struct super_block *d_sb;
 unsigned long d_time;
 void *d_fsdata;
 struct list_head d_lru;
 struct list_head d_child;
 struct list_head d_subdirs;
 union {
  struct hlist_node d_alias;
   struct callback_head d_rcu;
 } d_u;
};

struct file {
 union {
  struct llist_node fu_llist;
  struct callback_head fu_rcuhead;
 } f_u;
 struct path f_path;
 struct inode *f_inode;
 const struct file_operations *f_op;
 spinlock_t f_lock;
 atomic_long_t f_count;
 unsigned int f_flags;
 fmode_t f_mode;
 struct mutex f_pos_lock;
 loff_t f_pos;
 struct fown_struct f_owner;
 const struct cred *f_cred;
 struct file_ra_state f_ra;
 u64 f_version;
 void *f_security;
 void *private_data;
 struct list_head f_ep_links;
 struct list_head f_tfile_llink;
 struct address_space *f_mapping;
};

struct ida {
 struct idr idr;
 struct ida_bitmap *free_bitmap;
};

struct kset {
 struct list_head list;
 spinlock_t list_lock;
 struct kobject kobj;
 const struct kset_uevent_ops *uevent_ops;
};

struct list_lru {
 struct list_lru_node *node;
};

struct sysfs_ops {
 ssize_t (*show)(struct kobject *, struct attribute *, char *);
 ssize_t (*store)(struct kobject *, struct attribute *, const char *, size_t);
};

struct completion {
 unsigned int done;
 wait_queue_head_t wait;
};

struct dquot {
 struct hlist_node dq_hash;
 struct list_head dq_inuse;
 struct list_head dq_free;
 struct list_head dq_dirty;
 struct mutex dq_lock;
 atomic_t dq_count;
 wait_queue_head_t dq_wait_unused;
 struct super_block *dq_sb;
 struct kqid dq_id;
 loff_t dq_off;
 unsigned long dq_flags;
 struct mem_dqblk dq_dqb;
};

struct fasync_struct {
 spinlock_t fa_lock;
 int magic;
 int fa_fd;
 struct fasync_struct *fa_next;
 struct file *fa_file;
 struct callback_head fa_rcu;
};

struct iattr {
 unsigned int ia_valid;
 umode_t ia_mode;
 kuid_t ia_uid;
 kgid_t ia_gid;
 loff_t ia_size;
 struct timespec ia_atime;
 struct timespec ia_mtime;
 struct timespec ia_ctime;
 struct file *ia_file;
};

struct kernfs_open_file {
 struct kernfs_node *kn;
 struct file *file;
 void *priv;
 struct mutex mutex;
 int event;
 struct list_head list;
 char *prealloc_buf;
 size_t atomic_write_len;
 bool mmapped;
 const struct vm_operations_struct *vm_ops;
};

struct kernfs_root {
 struct kernfs_node *kn;
 unsigned int flags;
 struct ida ino_ida;
 struct kernfs_syscall_ops *syscall_ops;
 struct list_head supers;
 wait_queue_head_t deactivate_waitq;
};

struct kiocb {
 struct file *ki_filp;
 loff_t ki_pos;
 void (*ki_complete)(struct kiocb *iocb, long ret, long ret2);
 void *private;
 int ki_flags;
};

struct kobj_type {
 void (*release)(struct kobject *kobj);
 const struct sysfs_ops *sysfs_ops;
 struct attribute **default_attrs;
 const struct kobj_ns_type_operations *(*child_ns_type)(struct kobject *kobj);
 const void *(*namespace)(struct kobject *kobj);
};

struct sb_writers {
 struct percpu_counter counter[(SB_FREEZE_COMPLETE - 1)];
 wait_queue_head_t wait;
 int frozen;
 wait_queue_head_t wait_unfrozen;
};

struct vm_area_struct {
 unsigned long vm_start;
 unsigned long vm_end;
 struct vm_area_struct *vm_next, *vm_prev;
 struct rb_node vm_rb;
 unsigned long rb_subtree_gap;
 struct mm_struct *vm_mm;
 pgprot_t vm_page_prot;
 unsigned long vm_flags;
 struct {
  struct rb_node rb;
  unsigned long rb_subtree_last;
 } shared;
 struct list_head anon_vma_chain;
 struct anon_vma *anon_vma;
 const struct vm_operations_struct *vm_ops;
 unsigned long vm_pgoff;
 struct file * vm_file;
 struct file *vm_prfile;
 void * vm_private_data;
 struct mempolicy *vm_policy;
 struct vm_area_struct *vm_mirror;
};

struct address_space_operations {
 int (*writepage)(struct page *page, struct writeback_control *wbc);
 int (*readpage)(struct file *, struct page *);
 int (*writepages)(struct address_space *, struct writeback_control *);
 int (*set_page_dirty)(struct page *page);
 int (*readpages)(struct file *filp, struct address_space *mapping,
   struct list_head *pages, unsigned nr_pages);
 int (*write_begin)(struct file *, struct address_space *mapping,
    loff_t pos, unsigned len, unsigned flags,
    struct page **pagep, void **fsdata);
 int (*write_end)(struct file *, struct address_space *mapping,
    loff_t pos, unsigned len, unsigned copied,
    struct page *page, void *fsdata);
 sector_t (*bmap)(struct address_space *, sector_t);
 void (*invalidatepage) (struct page *, unsigned int, unsigned int);
 int (*releasepage) (struct page *, gfp_t);
 void (*freepage)(struct page *);
 ssize_t (*direct_IO)(struct kiocb *, struct iov_iter *iter, loff_t offset);
 int (*migratepage) (struct address_space *,
   struct page *, struct page *, enum migrate_mode);
 int (*launder_page) (struct page *);
 int (*is_partially_uptodate) (struct page *, unsigned long,
     unsigned long);
 void (*is_dirty_writeback) (struct page *, bool *, bool *);
 int (*error_remove_page)(struct address_space *, struct page *);
 int (*swap_activate)(struct swap_info_struct *sis, struct file *file,
    sector_t *span);
 void (*swap_deactivate)(struct file *file);
};

struct core_state {
 atomic_t nr_threads;
 struct core_thread dumper;
 struct completion startup;
};

struct file_lock {
 struct file_lock *fl_next;
 struct list_head fl_list;
 struct hlist_node fl_link;
 struct list_head fl_block;
 fl_owner_t fl_owner;
 unsigned int fl_flags;
 unsigned char fl_type;
 unsigned int fl_pid;
 int fl_link_cpu;
 struct pid *fl_nspid;
 wait_queue_head_t fl_wait;
 struct file *fl_file;
 loff_t fl_start;
 loff_t fl_end;
 struct fasync_struct * fl_fasync;
 unsigned long fl_break_time;
 unsigned long fl_downgrade_time;
 const struct file_lock_operations *fl_ops;
 const struct lock_manager_operations *fl_lmops;
 union {
  struct nfs_lock_info nfs_fl;
  struct nfs4_lock_info nfs4_fl;
  struct {
   struct list_head link;
   int state;
  } afs;
 } fl_u;
};

struct inode_operations {
 struct dentry * (*lookup) (struct inode *,struct dentry *, unsigned int);
 const char * (*follow_link) (struct dentry *, void **);
 int (*permission) (struct inode *, int);
 struct posix_acl * (*get_acl)(struct inode *, int);
 int (*readlink) (struct dentry *, char *,int);
 void (*put_link) (struct inode *, void *);
 int (*create) (struct inode *,struct dentry *, umode_t, bool);
 int (*link) (struct dentry *,struct inode *,struct dentry *);
 int (*unlink) (struct inode *,struct dentry *);
 int (*symlink) (struct inode *,struct dentry *,const char *);
 int (*mkdir) (struct inode *,struct dentry *,umode_t);
 int (*rmdir) (struct inode *,struct dentry *);
 int (*mknod) (struct inode *,struct dentry *,umode_t,dev_t);
 int (*rename) (struct inode *, struct dentry *,
   struct inode *, struct dentry *);
 int (*rename2) (struct inode *, struct dentry *,
   struct inode *, struct dentry *, unsigned int);
 int (*setattr) (struct dentry *, struct iattr *);
 int (*getattr) (struct vfsmount *mnt, struct dentry *, struct kstat *);
 int (*setxattr) (struct dentry *, const char *,const void *,size_t,int);
 ssize_t (*getxattr) (struct dentry *, const char *, void *, size_t);
 ssize_t (*listxattr) (struct dentry *, char *, size_t);
 int (*removexattr) (struct dentry *, const char *);
 int (*fiemap)(struct inode *, struct fiemap_extent_info *, u64 start,
        u64 len);
 int (*update_time)(struct inode *, struct timespec *, int);
 int (*atomic_open)(struct inode *, struct dentry *,
      struct file *, unsigned open_flag,
      umode_t create_mode, int *opened);
 int (*tmpfile) (struct inode *, struct dentry *, umode_t);
 int (*set_acl)(struct inode *, struct posix_acl *, int);
};

struct kernfs_ops {
 int (*seq_show)(struct seq_file *sf, void *v);
 void *(*seq_start)(struct seq_file *sf, loff_t *ppos);
 void *(*seq_next)(struct seq_file *sf, void *v, loff_t *ppos);
 void (*seq_stop)(struct seq_file *sf, void *v);
 ssize_t (*read)(struct kernfs_open_file *of, char *buf, size_t bytes,
   loff_t off);
 size_t atomic_write_len;
 bool prealloc;
 ssize_t (*write)(struct kernfs_open_file *of, char *buf, size_t bytes,
    loff_t off);
 int (*mmap)(struct kernfs_open_file *of, struct vm_area_struct *vma);
};

struct module_kobject {
 struct kobject kobj;
 struct module *mod;
 struct kobject *drivers_dir;
 struct module_param_attrs *mp;
 struct completion *kobj_completion;
};

struct quota_format_ops {
 int (*check_quota_file)(struct super_block *sb, int type);
 int (*read_file_info)(struct super_block *sb, int type);
 int (*write_file_info)(struct super_block *sb, int type);
 int (*free_file_info)(struct super_block *sb, int type);
 int (*read_dqblk)(struct dquot *dquot);
 int (*commit_dqblk)(struct dquot *dquot);
 int (*release_dqblk)(struct dquot *dquot);
};

struct address_space {
 struct inode *host;
 struct radix_tree_root page_tree;
 spinlock_t tree_lock;
 atomic_t i_mmap_writable;
 struct rb_root i_mmap;
 struct rw_semaphore i_mmap_rwsem;
 unsigned long nrpages;
 unsigned long nrshadows;
 unsigned long writeback_index;
 const struct address_space_operations *a_ops;
 unsigned long flags;
 spinlock_t private_lock;
 struct list_head private_list;
 void *private_data;
};

struct file_operations {
 struct module *owner;
 loff_t (*llseek) (struct file *, loff_t, int);
 ssize_t (*read) (struct file *, char *, size_t, loff_t *);
 ssize_t (*write) (struct file *, const char *, size_t, loff_t *);
 ssize_t (*read_iter) (struct kiocb *, struct iov_iter *);
 ssize_t (*write_iter) (struct kiocb *, struct iov_iter *);
 int (*iterate) (struct file *, struct dir_context *);
 unsigned int (*poll) (struct file *, struct poll_table_struct *);
 long (*unlocked_ioctl) (struct file *, unsigned int, unsigned long);
 long (*compat_ioctl) (struct file *, unsigned int, unsigned long);
 int (*mmap) (struct file *, struct vm_area_struct *);
 int (*mremap)(struct file *, struct vm_area_struct *);
 int (*open) (struct inode *, struct file *);
 int (*flush) (struct file *, fl_owner_t id);
 int (*release) (struct inode *, struct file *);
 int (*fsync) (struct file *, loff_t, loff_t, int datasync);
 int (*aio_fsync) (struct kiocb *, int datasync);
 int (*fasync) (int, struct file *, int);
 int (*lock) (struct file *, int, struct file_lock *);
 ssize_t (*sendpage) (struct file *, struct page *, int, size_t, loff_t *, int);
 unsigned long (*get_unmapped_area)(struct file *, unsigned long, unsigned long, unsigned long, unsigned long);
 int (*check_flags)(int);
 int (*flock) (struct file *, int, struct file_lock *);
 ssize_t (*splice_write)(struct pipe_inode_info *, struct file *, loff_t *, size_t, unsigned int);
 ssize_t (*splice_read)(struct file *, loff_t *, struct pipe_inode_info *, size_t, unsigned int);
 int (*setlease)(struct file *, long, struct file_lock **, void **);
 long (*fallocate)(struct file *file, int mode, loff_t offset,
     loff_t len);
 void (*show_fdinfo)(struct seq_file *m, struct file *f);
};

struct mm_struct {
 struct vm_area_struct *mmap;
 struct rb_root mm_rb;
 u32 vmacache_seqnum;
 unsigned long (*get_unmapped_area) (struct file *filp,
    unsigned long addr, unsigned long len,
    unsigned long pgoff, unsigned long flags);
 unsigned long mmap_base;
 unsigned long mmap_legacy_base;
 unsigned long task_size;
 unsigned long highest_vm_end;
 pgd_t * pgd;
 atomic_t mm_users;
 atomic_t mm_count;
 atomic_long_t nr_ptes;
 atomic_long_t nr_pmds;
 int map_count;
 spinlock_t page_table_lock;
 struct rw_semaphore mmap_sem;
 struct list_head mmlist;
 unsigned long hiwater_rss;
 unsigned long hiwater_vm;
 unsigned long total_vm;
 unsigned long locked_vm;
 unsigned long pinned_vm;
 unsigned long shared_vm;
 unsigned long exec_vm;
 unsigned long stack_vm;
 unsigned long def_flags;
 unsigned long start_code, end_code, start_data, end_data;
 unsigned long start_brk, brk, start_stack;
 unsigned long arg_start, arg_end, env_start, env_end;
 unsigned long saved_auxv[(2*(2 + 20 + 1))];
 struct mm_rss_stat rss_stat;
 struct linux_binfmt *binfmt;
 cpumask_var_t cpu_vm_mask_var;
 mm_context_t context;
 unsigned long flags;
 struct core_state *core_state;
 spinlock_t ioctx_lock;
 struct kioctx_table *ioctx_table;
 struct file *exe_file;
 bool tlb_flush_pending;
 struct uprobes_state uprobes_state;
};

struct module_attribute {
 struct attribute attr;
 ssize_t (*show)(struct module_attribute *, struct module_kobject *,
   char *);
 ssize_t (*store)(struct module_attribute *, struct module_kobject *,
    const char *, size_t count);
 void (*setup)(struct module *, const char *);
 int (*test)(struct module *);
 void (*free)(struct module *);
};

typedef struct module_attribute module_attribute_no_const;

struct inode {
 umode_t i_mode;
 unsigned short i_opflags;
 kuid_t i_uid;
 kgid_t i_gid;
 unsigned int i_flags;
 struct posix_acl *i_acl;
 struct posix_acl *i_default_acl;
 const struct inode_operations *i_op;
 struct super_block *i_sb;
 struct address_space *i_mapping;
 void *i_security;
 unsigned long i_ino;
 union {
  const unsigned int i_nlink;
  unsigned int __i_nlink;
 };
 dev_t i_rdev;
 loff_t i_size;
 struct timespec i_atime;
 struct timespec i_mtime;
 struct timespec i_ctime;
 spinlock_t i_lock;
 unsigned short i_bytes;
 unsigned int i_blkbits;
 blkcnt_t i_blocks;
 unsigned long i_state;
 struct mutex i_mutex;
 unsigned long dirtied_when;
 unsigned long dirtied_time_when;
 struct hlist_node i_hash;
 struct list_head i_wb_list;
 struct list_head i_lru;
 struct list_head i_sb_list;
 union {
  struct hlist_head i_dentry;
  struct callback_head i_rcu;
 };
 u64 i_version;
 atomic_t i_count;
 atomic_t i_dio_count;
 atomic_t i_writecount;
 const struct file_operations *i_fop;
 struct file_lock_context *i_flctx;
 struct address_space i_data;
 struct list_head i_devices;
 union {
  struct pipe_inode_info *i_pipe;
  struct block_device *i_bdev;
  struct cdev *i_cdev;
  char *i_link;
 };
 __u32 i_generation;
 __u32 i_fsnotify_mask;
 struct hlist_head i_fsnotify_marks;
 u32 digsig_flags;
 void *i_private;
};

struct dquot_operations {
 int (*write_dquot) (struct dquot *);
 struct dquot *(*alloc_dquot)(struct super_block *, int);
 void (*destroy_dquot)(struct dquot *);
 int (*acquire_dquot) (struct dquot *);
 int (*release_dquot) (struct dquot *);
 int (*mark_dirty) (struct dquot *);
 int (*write_info) (struct super_block *, int);
 qsize_t *(*get_reserved_space) (struct inode *);
 int (*get_projid) (struct inode *, kprojid_t *);
};

struct module {
 enum module_state state;
 struct list_head list;
 char name[(64 - sizeof(unsigned long))];
 struct module_kobject mkobj;
 module_attribute_no_const *modinfo_attrs;
 const char *version;
 const char *srcversion;
 struct kobject *holders_dir;
 const struct kernel_symbol *syms;
 const unsigned long *crcs;
 unsigned int num_syms;
 struct mutex param_lock;
 struct kernel_param *kp;
 unsigned int num_kp;
 unsigned int num_gpl_syms;
 const struct kernel_symbol *gpl_syms;
 const unsigned long *gpl_crcs;
 bool async_probe_requested;
 const struct kernel_symbol *gpl_future_syms;
 const unsigned long *gpl_future_crcs;
 unsigned int num_gpl_future_syms;
 unsigned int num_exentries;
 struct exception_table_entry *extable;
 int (*init)(void);
 void *module_init_rw ;
 void *module_init_rx;
 void *module_core_rx, *module_core_rw;
 unsigned int init_size_rw, core_size_rw;
 unsigned int init_size_rx, core_size_rx;
 struct mod_tree_node mtn_core_rw;
 struct mod_tree_node mtn_core_rx;
 struct mod_tree_node mtn_init_rw;
 struct mod_tree_node mtn_init_rx;
 struct mod_arch_specific arch;
 unsigned int taints;
 unsigned num_bugs;
 struct list_head bug_list;
 struct bug_entry *bug_table;
 Elf64_Sym *symtab, *core_symtab;
 unsigned int num_symtab, core_num_syms;
 char *strtab, *core_strtab;
 struct module_sect_attrs *sect_attrs;
 struct module_notes_attrs *notes_attrs;
 char *args;
 void *percpu;
 unsigned int percpu_size;
 unsigned int num_tracepoints;
 struct tracepoint * const *tracepoints_ptrs;
 unsigned int num_trace_bprintk_fmt;
 const char **trace_bprintk_fmt_start;
 struct trace_event_call **trace_events;
 unsigned int num_trace_events;
 struct trace_enum_map **trace_enums;
 unsigned int num_trace_enums;
 struct file_operations trace_id;
 struct file_operations trace_enable;
 struct file_operations trace_format;
 struct file_operations trace_filter;
 struct list_head source_list;
 struct list_head target_list;
 void (*exit)(void);
 atomic_t refcnt;
};

struct super_operations {
    struct inode *(*alloc_inode)(struct super_block *sb);
 void (*destroy_inode)(struct inode *);
    void (*dirty_inode) (struct inode *, int flags);
 int (*write_inode) (struct inode *, struct writeback_control *wbc);
 int (*drop_inode) (struct inode *);
 void (*evict_inode) (struct inode *);
 void (*put_super) (struct super_block *);
 int (*sync_fs)(struct super_block *sb, int wait);
 int (*freeze_super) (struct super_block *);
 int (*freeze_fs) (struct super_block *);
 int (*thaw_super) (struct super_block *);
 int (*unfreeze_fs) (struct super_block *);
 int (*statfs) (struct dentry *, struct kstatfs *);
 int (*remount_fs) (struct super_block *, int *, char *);
 void (*umount_begin) (struct super_block *);
 int (*show_options)(struct seq_file *, struct dentry *);
 int (*show_devname)(struct seq_file *, struct dentry *);
 int (*show_path)(struct seq_file *, struct dentry *);
 int (*show_stats)(struct seq_file *, struct dentry *);
 ssize_t (*quota_read)(struct super_block *, int, char *, size_t, loff_t);
 ssize_t (*quota_write)(struct super_block *, int, const char *, size_t, loff_t);
 struct dquot **(*get_dquots)(struct inode *);
 int (*bdev_try_to_free_page)(struct super_block*, struct page*, gfp_t);
 long (*nr_cached_objects)(struct super_block *,
      struct shrink_control *);
 long (*free_cached_objects)(struct super_block *,
        struct shrink_control *);
 struct file *(*real_loop)(struct file *);
};

struct file_system_type {
 const char *name;
 int fs_flags;
 struct dentry *(*mount) (struct file_system_type *, int,
         const char *, void *);
 void (*kill_sb) (struct super_block *);
 struct module *owner;
 struct file_system_type * next;
 struct hlist_head fs_supers;
 struct lock_class_key s_lock_key;
 struct lock_class_key s_umount_key;
 struct lock_class_key s_vfs_rename_key;
 struct lock_class_key s_writers_key[(SB_FREEZE_COMPLETE - 1)];
 struct lock_class_key i_lock_key;
 struct lock_class_key i_mutex_key;
 struct lock_class_key i_mutex_dir_key;
};

struct quota_format_type {
 int qf_fmt_id;
 const struct quota_format_ops *qf_ops;
 struct module *qf_owner;
 struct quota_format_type *qf_next;
};

struct ts_ops
{
 const char *name;
 struct ts_config * (*init)(const void *, unsigned int, gfp_t, int);
 unsigned int (*find)(struct ts_config *,
     struct ts_state *);
 void (*destroy)(struct ts_config *);
 void * (*get_pattern)(struct ts_config *);
 unsigned int (*get_pattern_len)(struct ts_config *);
 struct module *owner;
 struct list_head list;
};

struct mem_dqinfo {
 struct quota_format_type *dqi_format;
 int dqi_fmt_id;
 struct list_head dqi_dirty_list;
 unsigned long dqi_flags;
 unsigned int dqi_bgrace;
 unsigned int dqi_igrace;
 qsize_t dqi_max_spc_limit;
 qsize_t dqi_max_ino_limit;
 void *dqi_priv;
};

struct quota_info {
 unsigned int flags;
 struct mutex dqio_mutex;
 struct mutex dqonoff_mutex;
 struct inode *files[3];
 struct mem_dqinfo info[3];
 const struct quota_format_ops *ops[3];
};

struct super_block {
 struct list_head s_list;
 dev_t s_dev;
 unsigned char s_blocksize_bits;
 unsigned long s_blocksize;
 loff_t s_maxbytes;
 struct file_system_type *s_type;
 const struct super_operations *s_op;
 const struct dquot_operations *dq_op;
 const struct quotactl_ops *s_qcop;
 const struct export_operations *s_export_op;
 unsigned long s_flags;
 unsigned long s_iflags;
 unsigned long s_magic;
 struct dentry *s_root;
 struct rw_semaphore s_umount;
 int s_count;
 atomic_t s_active;
 void *s_security;
 const struct xattr_handler **s_xattr;
 struct list_head s_inodes;
 struct hlist_bl_head s_anon;
 struct list_head s_mounts;
 struct block_device *s_bdev;
 struct backing_dev_info *s_bdi;
 struct mtd_info *s_mtd;
 struct hlist_node s_instances;
 unsigned int s_quota_types;
 struct quota_info s_dquot;
 struct sb_writers s_writers;
 char s_id[32];
 u8 s_uuid[16];
 void *s_fs_info;
 unsigned int s_max_links;
 fmode_t s_mode;
 u32 s_time_gran;
 struct mutex s_vfs_rename_mutex;
 char *s_subtype;
 char *s_options;
 const struct dentry_operations *s_d_op;
 int cleancache_poolid;
 struct shrinker s_shrink;
 atomic_long_t s_remove_count;
 int s_readonly_remount;
 struct workqueue_struct *s_dio_done_wq;
 struct hlist_head s_pins;
 struct list_lru s_dentry_lru ;
 struct list_lru s_inode_lru ;
 struct callback_head rcu;
 int s_stack_depth;
 int forced_mac_level;
 int forced_mac_category;
 int forced_mac_inited;
        unsigned int s_secdel_rounds;
};
//------------------------------------------------------------------------------

static inline unsigned char __tolower(unsigned char c);

static inline unsigned char __toupper(unsigned char c);

static inline bool IS_ERR( const void *ptr);

static inline void *ts_config_priv(struct ts_config *conf);

static inline struct ts_config *alloc_ts_config(size_t payload, gfp_t gfp_mask);

extern void *memcpy(void *to, const void *from, size_t len);
//------------------------------------------------------------------------------

#define ASIZE 256

struct ts_bm
{
	u8 *		pattern;
	unsigned int	patlen;
	unsigned int 	bad_shift[ASIZE];
	unsigned int	good_shift[0];
};
//------------------------------------------------------------------------------

static int subpattern(u8 *pattern, int i, int j, int g)
{
	int x = i+g-1, y = j+g-1, ret = 0;

	while(pattern[x--] == pattern[y--]) {
		if (y < 0) {
			ret = 1;
			break;
		}
		if (--g == 0) {
			ret = pattern[i-1] != pattern[j-1];
			break;
		}
	}

	return ret;
}

static void compute_prefix_tbl(struct ts_bm *bm, int flags)
{
	int i, j, g;

	for (i = 0; i < ASIZE; i++)
		bm->bad_shift[i] = bm->patlen;
	for (i = 0; i < bm->patlen - 1; i++) {
		bm->bad_shift[bm->pattern[i]] = bm->patlen - 1 - i;
		if (flags & TS_IGNORECASE)
			bm->bad_shift[tolower(bm->pattern[i])]
			    = bm->patlen - 1 - i;
	}

	/* Compute the good shift array, used to match reocurrences 
	 * of a subpattern */
	bm->good_shift[0] = 1;
	for (i = 1; i < bm->patlen; i++)
		bm->good_shift[i] = bm->patlen;
        for (i = bm->patlen-1, g = 1; i > 0; g++, i--) {
		for (j = i-1; j >= 1-g ; j--)
			if (subpattern(bm->pattern, i, j, g)) {
				bm->good_shift[g] = bm->patlen-j-g;
				break;
			}
	}
}

static unsigned int bm_find(struct ts_config *conf, struct ts_state *state)
{
	struct ts_bm *bm = ts_config_priv(conf);
	unsigned int i, text_len, consumed = state->offset;
	const u8 *text;
	int shift = bm->patlen - 1, bs;
	const u8 icase = conf->flags & TS_IGNORECASE;

	for (;;) {
		text_len = conf->get_next_block(consumed, &text, conf, state);

		if (unlikely(text_len == 0))
			break;

		while (shift < text_len) {
			DEBUGP("Searching in position %d (%c)\n", 
				shift, text[shift]);
			for (i = 0; i < bm->patlen; i++) 
				if ((icase ? toupper(text[shift-i])
				    : text[shift-i])
					!= bm->pattern[bm->patlen-1-i])
				     goto next;

			/* London calling... */
			DEBUGP("found!\n");
			return consumed += (shift-(bm->patlen-1));

next:			bs = bm->bad_shift[text[shift-i]];

			/* Now jumping to... */
			shift = max_t(int, shift-i+bs, shift+bm->good_shift[i]);
		}
		consumed += text_len;
	}

	return UINT_MAX;
}

static struct ts_config *bm_init(const void *pattern, unsigned int len,
				 gfp_t gfp_mask, int flags)
{
	struct ts_config *conf;
	struct ts_bm *bm;
	int i;
	unsigned int prefix_tbl_len = len * sizeof(unsigned int);
	size_t priv_size = sizeof(*bm) + len + prefix_tbl_len;

	conf = alloc_ts_config(priv_size, gfp_mask);
	if (IS_ERR(conf))
		return conf;

	conf->flags = flags;
	bm = ts_config_priv(conf);
	bm->patlen = len;
	bm->pattern = (u8 *) bm->good_shift + prefix_tbl_len;
	if (flags & TS_IGNORECASE)
		for (i = 0; i < len; i++)
			bm->pattern[i] = toupper(((u8 *)pattern)[i]);
	else
		memcpy(bm->pattern, pattern, len);
	compute_prefix_tbl(bm, flags);

	return conf;
}
