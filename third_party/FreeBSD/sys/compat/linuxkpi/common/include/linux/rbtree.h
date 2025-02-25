/*-
 * Copyright (c) 2010 Isilon Systems, Inc.
 * Copyright (c) 2010 iX Systems, Inc.
 * Copyright (c) 2010 Panasas, Inc.
 * Copyright (c) 2013, 2014 Mellanox Technologies, Ltd.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice unmodified, this list of conditions, and the following
 *    disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES
 * OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
 * IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
 * NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
 * THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 * $FreeBSD$
 */
#ifndef	_LINUXKPI_LINUX_RBTREE_H_
#define	_LINUXKPI_LINUX_RBTREE_H_

#include <linux/list.h>
#include <linux/tree.h>
#include <sys/types.h>

#ifdef __cplusplus
#if __cplusplus
extern "C" {
#endif /* __cplusplus */
#endif /* __cplusplus */

struct rb_node {
    RB_ENTRY(rb_node)    __entry;
};
#define    rb_left           __entry.rbe_left
#define    rb_right          __entry.rbe_right
#define    rb_parent_color   __entry.rbe_color
/*
 * We provide a false structure that has the same bit pattern as tree.h
 * presents so it matches the member names expected by linux.
 */
struct rb_root {
    struct    rb_node    *rb_node;
};

struct rb_root_cached {
	struct rb_root rb_root;
	struct rb_node *rb_leftmost;
};

/*
 * In linux all of the comparisons are done by the caller.
 */
int panic_cmp(struct rb_node *one, struct rb_node *two);

RB_HEAD(linux_root, rb_node);
RB_PROTOTYPE(linux_root, rb_node, __entry, panic_cmp);

#define    rb_parent(r)    RB_PARENT(r, __entry)
#define    rb_color(r)    RB_COLOR(r, __entry)
#define    rb_is_red(r)    (rb_color(r) == RB_RED)
#define    rb_is_black(r)    (rb_color(r) == RB_BLACK)
#define    rb_set_parent(r, p)    rb_parent((r)) = (p)
#define    rb_set_color(r, c)    rb_color((r)) = (c)
#define    rb_entry(ptr, type, member)    LOS_DL_LIST_ENTRY(ptr, type, member)

#define RB_EMPTY_ROOT(root)     RB_EMPTY((struct linux_root *)root)
#define RB_EMPTY_NODE(node)     (rb_parent(node) == node)
#define RB_CLEAR_NODE(node)     (rb_set_parent(node, node))

#define    rb_insert_color(node, root)                    \
    linux_root_RB_INSERT_COLOR((struct linux_root *)(root), (node))
#define    rb_erase(node, root)                        \
    (void)linux_root_RB_REMOVE((struct linux_root *)(root), (node))
#define    rb_next(node)    RB_NEXT(linux_root, NULL, (node))
#define    rb_prev(node)    RB_PREV(linux_root, NULL, (node))
#define    rb_first(root)    RB_MIN(linux_root, (struct linux_root *)(root))
#define	rb_last(root)	RB_MAX(linux_root, (struct linux_root *)(root))
#define	rb_first_cached(root)	(root)->rb_leftmost

static inline void
rb_link_node(struct rb_node *node, struct rb_node *parent,
    struct rb_node **rb_link)
{
    rb_set_parent(node, parent);
    rb_set_color(node, RB_RED);
    node->__entry.rbe_left = node->__entry.rbe_right = NULL;
    *rb_link = node;
}

static inline void
rb_replace_node(struct rb_node *victim, struct rb_node *newnode,
    struct rb_root *root)
{
    struct rb_node *p;

    p = rb_parent(victim);
    if (p) {
        if (p->rb_left == victim)
            p->rb_left = newnode;
        else
            p->rb_right = newnode;
    } else
        root->rb_node = newnode;
    if (victim->rb_left)
        rb_set_parent(victim->rb_left, newnode);
    if (victim->rb_right)
        rb_set_parent(victim->rb_right, newnode);
    *newnode = *victim;
}

static inline void
rb_insert_color_cached(struct rb_node *node, struct rb_root_cached *root,
    bool leftmost)
{
	linux_root_RB_INSERT_COLOR((struct linux_root *)&root->rb_root, node);
	if (leftmost)
		root->rb_leftmost = node;
}

static inline struct rb_node *
rb_erase_cached(struct rb_node *node, struct rb_root_cached *root)
{
	struct rb_node *retval;

	if (node == root->rb_leftmost)
		retval = root->rb_leftmost = linux_root_RB_NEXT(node);
	else
		retval = NULL;
	linux_root_RB_REMOVE((struct linux_root *)&root->rb_root, node);
	return (retval);
}

static inline void
rb_replace_node_cached(struct rb_node *old, struct rb_node *new,
    struct rb_root_cached *root)
{
	rb_replace_node(old, new, &root->rb_root);
	if (root->rb_leftmost == old)
		root->rb_leftmost = new;
}

#undef RB_ROOT
#define RB_ROOT        (struct rb_root) { NULL }
#define	RB_ROOT_CACHED	(struct rb_root_cached) { RB_ROOT, NULL }

#ifdef __cplusplus
#if __cplusplus
}
#endif /* __cplusplus */
#endif /* __cplusplus */

#endif    /* _LINUXKPI_LINUX_RBTREE_H_ */
