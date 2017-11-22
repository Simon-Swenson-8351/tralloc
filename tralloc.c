/*
 * A binary tree based memory allocator.
 * 
 * Copyright 2017 Simon Swenson. All rights reserved.
 * 
 * License: BSD License
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *     * Redistributions of source code must retain the above copyright notice,
 *       this list of conditions and the following disclaimer.
 *     * Redistributions in binary form must reproduce the above copyright
 *       notice, this list of conditions and the following disclaimer in the
 *       documentation and/or other materials provided with the distribution.
 *     * Neither the name of the organization nor the names of its contributors
 *       may be used to endorse or promote products derived from this software
 *       without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED. IN NO EVENT SHALL COPYRIGHT HOLDER BE LIABLE FOR ANY DIRECT,
 * INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 * ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

#include "tralloc.h"
#include <unistd.h>
#include <stdbool.h>

// Struct definitions
typedef struct header {
    size_t size;
    bool in_use;
} header;

typedef struct node {
    header *parent;
    header *left;
    header *right;
} node;

typedef struct footer {
    size_t size;
} footer;

// Function prototypes
static inline node *header_to_node(header *input);
static inline footer *header_to_footer(header *input);
static inline header *node_to_header(node *input);
static inline footer *node_to_footer(node *input);
static inline header *footer_to_header(footer *input);
static inline node *footer_to_node(footer *input);
static inline size_t ceil_size(size_t input, size_t offset);

static header *add_chunk(header *tree, header *to_add, header* parent_chunk);
// Will find a node that's an equal size or larger than the given size, then remove it.
static header *remove_chunk_by_size(header *tree, size_t size);
// to_remove is assumed not to be NULL.
static void remove_chunk(header *to_remove);

// It is assumed that find_replacement will be called on a tree with populated left and right subtrees.
static header *find_replacement(header *tree);
// It is assumed that tree is not NULL.
static header *find_largest(header *tree);
// It is assumed that tree is not NULL.
static header *find_smallest(header *tree);

static void fprint_tree(FILE *f, header *tree, int depth);
static inline void fprint_depth_padding(FILE *f, int depth);

// Global variables
static header *fake_root = NULL;
static void *first_chunk = NULL;
static void *guard_addr = NULL;
static size_t header_pad = 0;
static size_t footer_pad = 0;
static size_t node_pad = 0;

// If the size of the chunk we're adding to the tree is the same as another chunk, we alternate whether we will put the added chunk in the left or right child.
static bool equals_alternator = false;
// Deciding whether we take the successor or predecessor in find_replacement
static bool succ_pred_alternator = false;

void *tralloc(size_t size) {
    // init globals
    if(!header_pad)
        header_pad = ceil_size(sizeof(header), sizeof(intptr_t));
    if(!footer_pad)
        footer_pad = ceil_size(sizeof(footer), sizeof(intptr_t));
    if(!node_pad)
        node_pad = ceil_size(sizeof(node), sizeof(intptr_t));
    if(!fake_root) {
        fake_root = (header *)sbrk(header_pad + node_pad);
        fake_root->size = 0;
        fake_root->in_use = false;
        node *fake_root_node = header_to_node(fake_root);
        fake_root_node->parent = NULL;
        fake_root_node->left = NULL;
        fake_root_node->right = NULL;
    }
    
    size = ceil_size(size, sizeof(intptr_t));
    // size to allocate is too small. Make it at least big enough to hold a node.
    if(size < node_pad) size = node_pad;

    // Try to find a node already in the tree
    header *found = remove_chunk_by_size(fake_root, size);
    if(!found) {
        // Need to allocate for another chunk.
        found = (header *)sbrk(header_pad + size + footer_pad);
        if(!first_chunk) first_chunk = (void *)found;
        guard_addr = (void *)((char *)found + header_pad + size + footer_pad);
        found->size = size;
        header_to_footer(found)->size = size;
    } else if(found->size >= size + footer_pad + header_pad + node_pad) {
        // There was a returned chunk, and that chunk has a dividend. (It's large enough to be divided.)
        header *dividend = (header *)((char *)found + header_pad + size + footer_pad);
        dividend->size = found->size - size - footer_pad - header_pad;
        dividend->in_use = false;
        header_to_footer(dividend)->size = dividend->size;
        fake_root = add_chunk(fake_root, dividend, NULL);

        found->size = size;
        header_to_footer(found)->size = size;
    }
    found->in_use = true;
    return (void *)header_to_node(found);
}

void trfree(void *to_free) {
    header *to_free_chunk = node_to_header((node *)to_free);
    header *concat_candidate = NULL;
    if(to_free_chunk != first_chunk) {
        // We are not the first chunk in memory, and thus the previous chunk exists.
        concat_candidate = footer_to_header((footer *)((char *)to_free_chunk - footer_pad));
        if(!(concat_candidate->in_use)) {
            // The previous chunk is free, so we can "sew" it together with this newly-freed chunk.
            remove_chunk(concat_candidate);
            concat_candidate->size += footer_pad + header_pad + to_free_chunk->size;
            header_to_footer(concat_candidate)->size = concat_candidate->size;
            // Need to reassign to_free_chunk to play nicely when we check to see if the next chunk is free, as well.
            to_free_chunk = concat_candidate;
        }
    }
    if((char *)header_to_footer(to_free_chunk) + footer_pad != guard_addr) {
        // We are not the last chunk in memory, and thus the next chunk exists.
        concat_candidate = (header *)((char *)header_to_footer(to_free_chunk) + footer_pad);
        if(!(concat_candidate->in_use)) {
            // The next chunk is free, so we can "sew" it together with this newly-freed chunk.
            remove_chunk(concat_candidate);
            to_free_chunk->size += footer_pad + header_pad + concat_candidate->size;
            header_to_footer(to_free_chunk)->size = to_free_chunk->size;
        }
    }
    to_free_chunk->in_use = false;
    fake_root = add_chunk(fake_root, to_free_chunk, NULL);
}

static header *add_chunk(header *tree, header *to_add, header *parent_chunk) {
    node *tree_node = header_to_node(tree);
    if(!tree) {
        to_add->in_use = false;
        node *to_add_node = header_to_node(to_add);
        to_add_node->left = NULL;
        to_add_node->right = NULL;
        to_add_node->parent = parent_chunk;
        return to_add;
    }
    if(to_add->size < tree->size) {
        tree_node->left = add_chunk(tree_node->left, to_add, tree);
    } else if(to_add->size > tree->size) {
        tree_node->right = add_chunk(tree_node->right, to_add, tree);
    } else {
        if(equals_alternator) tree_node->left = add_chunk(tree_node->left, to_add, tree);
        else tree_node->right = add_chunk(tree_node->right, to_add, tree);
        equals_alternator = !equals_alternator;
    }
    return tree;
}

static header *remove_chunk_by_size(header *tree, size_t size) {
    if(!tree) return NULL; // Didn't find a good node.
    node *tree_node = header_to_node(tree);
    if(tree->size < size) {
        return remove_chunk_by_size(tree_node->right, size);
    } else {
        remove_chunk(tree);
        return tree;
    }
}

static void remove_chunk(header *to_remove) {
    node *to_remove_node = header_to_node(to_remove);
    node *parent_node = header_to_node(to_remove_node->parent);
    header **parents_child_member;
    if(parent_node->left == to_remove) parents_child_member = &(parent_node->left);
    else parents_child_member = &(parent_node->right);
    if(to_remove_node->left) {
        if(to_remove_node->right) {
            header *replacement = find_replacement(to_remove);
            node *replacement_node = header_to_node(replacement);
            remove_chunk(replacement);
            replacement_node->parent = to_remove_node->parent;
            replacement_node->left = to_remove_node->left;
            replacement_node->right = to_remove_node->right;
            *parents_child_member = replacement;
            if(to_remove_node->right)
                header_to_node(to_remove_node->right)->parent = replacement;
            if(to_remove_node->left)
                header_to_node(to_remove_node->left)->parent = replacement;
        } else {
            *parents_child_member = to_remove_node->left;
            header_to_node(to_remove_node->left)->parent = to_remove_node->parent;
        }
    } else {
        if(to_remove_node->right) {
            *parents_child_member = to_remove_node->right;
            header_to_node(to_remove_node->right)->parent = to_remove_node->parent;
        } else {
            *parents_child_member = NULL;
        }
    }
}

static header *find_replacement(header *tree) {
    node *tree_node = header_to_node(tree);
    succ_pred_alternator = !succ_pred_alternator;
    if(succ_pred_alternator) return find_largest(tree_node->left);
    else return find_smallest(tree_node->right);
}

static header *find_largest(header *tree) {
    node *tree_node = header_to_node(tree);
    if(!tree_node->right) return tree;
    else return find_largest(tree_node->right);
}

static header *find_smallest(header *tree) {
    node *tree_node = header_to_node(tree);
    if(!tree_node->left) return tree;
    else return find_smallest(tree_node->left);
}

static inline size_t ceil_size(size_t input, size_t offset) {
    if(input % offset) return input - (input % offset) + offset;
    return input;
}

static inline node *header_to_node(header *input) { return (node *)((char *)input + header_pad); }
static inline footer *header_to_footer(header *input) { return (footer *)((char *)input + header_pad + input->size); }
static inline header *node_to_header(node *input) { return (header *)((char *)input - header_pad); }
static inline footer *node_to_footer(node *input) { return (footer *)((char *)input + node_to_header(input)->size); }
static inline header *footer_to_header(footer *input) { return (header *)((char *)input - input->size - header_pad); }
static inline node *footer_to_node(footer *input) { return (node *)((char *)input - input->size); }

void traudit(FILE *f) {
    fprintf(f, "traudit begin\n");
    fprintf(f, "fake_root: %p\n", fake_root);
    fprintf(f, "first_chunk: %p\n", first_chunk);
    fprintf(f, "guard_addr: %p\n", guard_addr);
    fprintf(f, "header_pad: %lu\n", header_pad);
    fprintf(f, "footer_pad: %lu\n", footer_pad);
    fprintf(f, "node_pad: %lu\n", node_pad);
    if(!(first_chunk && guard_addr)) goto traudit_end;
    header *cur = (header *)first_chunk;
    node *cur_node = header_to_node(cur);
    footer *cur_footer = header_to_footer(cur);
    while(true) {
        fprintf(f, "    chunk: %p\n    chunk->size: %lu\n    chunk->in_use: %u\n", cur, cur->size, cur->in_use);
        if(cur->in_use) {
            int *i;
            for(i = (int *)cur_node; (footer *)i != cur_footer; i++) {
                fprintf(f, "        data: %x\n", *i);
            }
        } else {
            // Should be in the free tree
            fprintf(f, "    chunk_node->parent: %p\n    chunk_node->left: %p\n    chunk_node->right: %p\n", cur_node->parent, cur_node->left, cur_node->right);
        }
        fprintf(f, "    chunk_footer->size: %lu\n", cur->size);
        if((char *)header_to_footer(cur) + footer_pad == guard_addr)
            break;
        cur = (header *)((char *)cur_footer + footer_pad);
        cur_node = header_to_node(cur);
        cur_footer = header_to_footer(cur);
    }
    fprint_tree(f, fake_root, 0);
    traudit_end: fprintf(f, "traudit end\n");
}

static void fprint_tree(FILE *f, header *tree, int depth) {
    fflush(f);
    if(!tree) {
        fprint_depth_padding(f, depth);
        fprintf(f, "NULL\n");
        return;
    }
    node *tree_node = header_to_node(tree);
    fprint_depth_padding(f, depth);
    fprintf(f, "(chunk: %p,\n", tree);
    fprint_depth_padding(f, depth);
    fprintf(f, "chunk->size: %lu,\n", tree->size);
    fprint_depth_padding(f, depth);
    fprintf(f, "chunk->in_use: %u,\n", tree->in_use);
    fprint_depth_padding(f, depth);
    fprintf(f, "chunk_node->parent: %p,\n", tree_node->parent);
    fprint_depth_padding(f, depth);
    fprintf(f, "chunk_node->left:\n");
    fprint_tree(f, tree_node->left, depth + 1);
    fprint_depth_padding(f, depth);
    fprintf(f, "chunk_node->right:\n");
    fprint_tree(f, tree_node->right, depth + 1);
    fprint_depth_padding(f, depth);
    fprintf(f, ")\n");
}

static inline void fprint_depth_padding(FILE *f, int depth) {
    int i;
    for(i = 0; i < depth * 4; i++) fprintf(f, " ");
}