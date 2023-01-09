/*
 * mm.c
 *
 * Name: 马江岩
 * ID: 2000012707
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#define DEBUG
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)
#define ALIGN_ODD(p) (((size_t)(p) & ~0x1) + 1)

#define MAX(x, y) ((x) > (y)? (x) : (y))
#define MIN(x, y) ((x) < (y)? (x) : (y))

#define TAG_ALLOC(ptr, size) (((int *)(ptr))[0] = (size) ^ 0x4)
#define TAG_PREV_ALLOC_PTR(ptr) (((int *)(ptr))[0] &= ~1)
#define TAG_PREV_FREE_PTR(ptr) (((int *)(ptr))[0] |= 1)
#define TAG_PREV_ALLOC(ptr) \
	TAG_PREV_ALLOC_PTR((ptr) == mem_heap_hi() + 1 ? &hi_tag : (ptr))
#define TAG_PREV_FREE(ptr) \
	TAG_PREV_FREE_PTR((ptr) == mem_heap_hi() + 1 ? &hi_tag : (ptr))

#define TAG_FREE_8(ptr) (((long *)(ptr))[0] = 8LL << 32 | 3)
#define TAG_FREE(ptr, size) (((int *)(ptr))[3] = \
		((int *)((ptr) + (size)))[-1] = (size))
#define TAG_FREE_LIST(ptr) (((int *)(ptr))[0] = 2)

#define ALLOC_TAG(ptr) (((int *)(ptr))[0] & 0x4)
#define ALLOC_SIZE(ptr) (((int *)(ptr))[0] & ~0x7)

#define FREE_TYPE(ptr) (((int *)(ptr))[0] & 0x3)
#define FREE_PREV(ptr) ((int *)(ptr))[1]
#define FREE_NEXT(ptr) ((int *)(ptr))[2]
#define FREE_SIZE(ptr) ((int *)(ptr))[3]

#define FREE_CHILD(ptr, lr) ((int *)(ptr))[lr]
#define FREE_CHILDREN(ptr) ((long *)(ptr))[0]

#define PREV_FREE_TAG(ptr) (((int *)(ptr))[0] & 0x1)
#define PREV_FREE_SIZE(ptr) (((int *)(ptr))[-1])

#define THRESHOLD 30
#define BLOCKSIZE 8192

static void *heap_start;
static int *link_start;
static int splay_root;
static int hi_tag;
static int in_heap(const void *p);
static int splay_rotate(int node, int lr);
static int splay_insert(int node, void *ptr);
static int splay_search(int node, int size);
static void splay_remove();
static void free_insert(void *ptr, int size);
static void *free_search(int size);
static void free_remove(void *ptr);
static void extend_heap(int size);
static void coalesce(void *ptr, int size);


/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void)
{
    link_start = mem_sbrk(ALIGN_ODD(THRESHOLD) * 4);
    for (int i = 0; i < THRESHOLD; i++)link_start[i] = 1;
    heap_start = mem_heap_hi() + 1;
    splay_root = 1;
    hi_tag = 0;
    return 0;
}


/*
 * malloc
 */
void *malloc(size_t size)
{
    if (size == 0)return NULL;
    size = ALIGN(size + 4);
    void *ptr = free_search((int)size);
    int remain;
    if (ptr)
    {
        free_remove(ptr);
        remain = FREE_SIZE(ptr) - size;
        free_insert(ptr + size, remain);
        TAG_ALLOC(ptr, size);
    }
    else
    {
        ptr = mem_heap_hi() + 1;
        if (hi_tag)
        {
            remain = PREV_FREE_SIZE(ptr);
            ptr -= remain;
            if (remain != 8)free_remove(ptr);
            hi_tag = 0;
            extend_heap(size - remain);
        }
        else extend_heap(size);
        TAG_ALLOC(ptr, size);
    }
    return ptr + 4;
}


/*
 * free
 */
void free(void *ptr)
{
    if (!in_heap(ptr))return;
    ptr -= 4;
    int size = ALLOC_SIZE(ptr);
    coalesce(ptr, size);
}


/*
 * realloc - you may want to look at mm-naive.c
 */
void *realloc(void *oldptr, size_t size)
{
    if (oldptr == NULL)return malloc(size);
    if (size == 0)
    {
        free(oldptr);
        return 0;
    }
    oldptr -= 4;
    int old_size = ALLOC_SIZE(oldptr);
    int prev_free = PREV_FREE_TAG(oldptr);
    size = ALIGN(MAX(size, 8) + 4);
    if ((int)size == old_size)return oldptr + 4;
    else if ((int)size < old_size)
    {
        TAG_ALLOC(oldptr, size);
        if (prev_free)TAG_PREV_FREE(oldptr);
        void *next = oldptr + old_size;
        int next_size = old_size - size;
        if (next <= mem_heap_hi() && !ALLOC_TAG(next))
        {
            if (FREE_TYPE(next) == 3)next_size += 8;
            else
            {
                free_remove(next);
                next_size += FREE_SIZE(next);
            }
        }
        free_insert(oldptr + size, next_size);
        return oldptr + 4;
    }
    else if (oldptr + old_size == mem_heap_hi() + 1)
    {
        extend_heap(size - old_size);
        TAG_ALLOC(oldptr, size);
        if (prev_free)TAG_PREV_FREE(oldptr);
        return oldptr + 4;
    }
    else if (!ALLOC_TAG(oldptr + old_size) && 
             (FREE_TYPE(oldptr + old_size) == 3 ?
              8 : FREE_SIZE(oldptr + old_size)) + old_size >= (int)size)
    {
        if (FREE_TYPE(oldptr + old_size) == 3)old_size += 8;
        else
        {
            free_remove(oldptr + old_size);
            old_size += FREE_SIZE(oldptr + old_size);
        }
        TAG_ALLOC(oldptr, size);
        if (prev_free)TAG_PREV_FREE(oldptr);
        free_insert(oldptr + size, old_size - size);
        return oldptr + 4;
    }
    else
    {
        void *new_ptr = malloc(size - 4);
        memcpy(new_ptr, oldptr + 4, old_size - 4);
        free(oldptr + 4);
        return new_ptr;
    }
}


/*
 * calloc - you may want to look at mm-naive.c
 * This function is not tested by mdriver, but it is
 * needed to run the traces.
 */
void *calloc(size_t nmemb, size_t size)
{
    size_t bytes = nmemb * size;
    void *new_ptr;
    new_ptr = malloc(bytes);
    memset(new_ptr, 0, bytes);
    return new_ptr;
}


static int splay_rotate(int node, int lr)
{
    int child = FREE_CHILD(heap_start + node, lr);
    FREE_CHILD(heap_start + node, lr) = FREE_CHILD(heap_start + child, !lr);
    FREE_CHILD(heap_start + child, !lr) = node;
    return child;
}


static int splay_insert(int node, void *ptr)
{
    if (node == 1)
    {
        FREE_CHILDREN(ptr) = 1LL << 32 | 1LL;
        FREE_NEXT(ptr) = 1;
        return ptr - heap_start;
    }
    void *node_ptr = heap_start + node;
    if (FREE_SIZE(node_ptr) == FREE_SIZE(ptr))
    {
        FREE_CHILDREN(ptr) = FREE_CHILDREN(node_ptr);
        FREE_NEXT(ptr) = node;
        TAG_FREE_LIST(node_ptr);
        FREE_PREV(node_ptr) = ptr - heap_start;
        return ptr - heap_start;
    }
    int lr = FREE_SIZE(node_ptr) < FREE_SIZE(ptr);
    FREE_CHILD(node_ptr, lr) = splay_insert(FREE_CHILD(node_ptr, lr), ptr);
    return node;
}


static int splay_search(int node, int size)
{
    if (node == 1)return 1;
    void *node_ptr = heap_start + node;
    int lr = size > FREE_SIZE(node_ptr);
    if (FREE_SIZE(node_ptr) == size)return node;
    FREE_CHILD(node_ptr, lr) = splay_search(FREE_CHILD(node_ptr, lr), size);
    if (FREE_CHILD(node_ptr, lr) == 1)return node;
    if (size == ~0U >> 1)return splay_rotate(node, lr);
    if (size <= FREE_SIZE(heap_start + FREE_CHILD(node_ptr, lr)))
        return splay_rotate(node, lr);
    return node;
}


static void splay_remove()
{
    int rchild = FREE_CHILD(heap_start + splay_root, 1);
    splay_root = FREE_CHILD(heap_start + splay_root, 0);
    if (splay_root == 1)splay_root = rchild;
    else
    {
        splay_root = splay_search(splay_root, ~0U >> 1);
        FREE_CHILD(heap_start + splay_root, 1) = rchild;
    }
}


static void free_insert(void *ptr, int size)
{
    int *link;
    if (size > (THRESHOLD + 1) << 3)
    {
        TAG_FREE(ptr, size);
        splay_root = splay_insert(splay_root, ptr);
        TAG_PREV_FREE(ptr + size);
    }
    else if (size >= 16)
    {
        TAG_FREE(ptr, size);
        link = link_start + ((size - 16) >> 3);
        if (*link != 1)
        {
            TAG_FREE_LIST(heap_start + *link);
            FREE_PREV(heap_start + *link) = ptr - heap_start;
        }
        FREE_CHILD(ptr, 0) = 0;
        FREE_NEXT(ptr) = *link;
        *link = ptr - heap_start;
        TAG_PREV_FREE(ptr + size);
    }
    else if (size)
    {
        TAG_FREE_8(ptr);
        TAG_PREV_FREE(ptr + size);
    }
    else TAG_PREV_ALLOC(ptr + size);
}


static void *free_search(int size)
{
    size = MAX(size, 16);
    for (int i = (size >> 3) - 2; i < THRESHOLD; i++)
        if (link_start[i] != 1)return heap_start + link_start[i];
    splay_root = splay_search(splay_root, size);
    if (splay_root == 1)return NULL;
    if (size > FREE_SIZE(heap_start + splay_root))return NULL;
    return heap_start + splay_root;
}


static void free_remove(void *ptr)
{
    int next;
    if (FREE_TYPE(ptr) == 2)
    {
        FREE_NEXT(heap_start + FREE_PREV(ptr)) = next = FREE_NEXT(ptr);
        if (next != 1)FREE_PREV(heap_start + next) = FREE_PREV(ptr);
    }
    else if (FREE_SIZE(ptr) <= (THRESHOLD + 1) << 3)
    {
        link_start[(FREE_SIZE(ptr) - 16) >> 3] = next = FREE_NEXT(ptr);
        if (next != 1)FREE_CHILD(heap_start + next, 0) = 0;
    }
    else
    {
        free_search(FREE_SIZE(ptr));
        next = FREE_NEXT(ptr);
        if (next != 1)
        {
            FREE_CHILDREN(heap_start + next) = FREE_CHILDREN(ptr);
            splay_root = next;
        }
        else splay_remove();
    }
}


static void extend_heap(int size)
{
    if (size < BLOCKSIZE)
    {
        int remain = BLOCKSIZE - size;
        mem_sbrk(BLOCKSIZE);
        free_insert(mem_heap_hi() + 1 - remain, remain);
    }
    else mem_sbrk(size);
}


static void coalesce(void *ptr, int size)
{
    if (PREV_FREE_TAG(ptr))
    {
        int prev_size = PREV_FREE_SIZE(ptr);
        size += prev_size;
        ptr -= prev_size;
        if (prev_size != 8)free_remove(ptr);
    }
    void *next = ptr + size;
    if (next <= mem_heap_hi() && !ALLOC_TAG(next))
    {
        if (FREE_TYPE(next) == 3)size += 8;
        else
        {
            free_remove(next);
            size += FREE_SIZE(next);
        }
    }
    free_insert(ptr, size);
}


/*
 * Return whether the pointer is in the heap.
 * May be useful for debugging.
 */
static int in_heap(const void *p)
{
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}


/*
 * Return whether the pointer is aligned.
 * May be useful for debugging.
 */
static int aligned(const void *p)
{
    return (size_t)ALIGN(p) == (size_t)p;
}


/*
 * mm_checkheap
 */
void mm_checkheap(int lineno)
{
    
}