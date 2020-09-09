#include <assert.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define SW 0
#define SE 1
#define NW 2
#define NE 3
#define WHITE 0
#define BLACK 1
#define GRAY 2
#define SEPARATE 0
#define INTERSECT 1
#define TOUCHING 2
#define MAX(a,b) (((a)>(b))?(a):(b))
#define MIN(a,b) (((a)<(b))?(a):(b))
#define ABS(a) (((a)>0)?(a):(-(a)))
#define EPS 1e-6
#define MAX_DEPTH 5
#define WIDTH (1<<MAX_DEPTH)
#define PM_TYPE 1
#define BF_CHECK 1
#define DISPLAY 1
#define ALL_DISPLAY 0
#define STATIC 1
#define DASH_BLACK 1
#define DASH_WHITE 1
#define DOT_RADIUS 2
#define MAX_BUFFER ((int)1e6)
#define OP_TYPE 9
#define MAX_POINTS 20000

typedef struct point {
    double x, y;
    char name[8];
} point;

typedef struct edge {
    point *a, *b;
    char name[16];
    int deleted;
} edge;

typedef struct list {
    edge *e;
    struct list *next;
} list;

typedef struct quad {
    struct quad *child[4];
    point A, B;
    list *edges;
} quad;

typedef struct bst {
    edge *e;
    struct bst *left, *right;
    int h, s;
} bst;

typedef struct heap {
    void *n;
    double key;
    struct heap *head, *next, *prev;
} heap;

int list_count, quad_count, bst_count, heap_count;
void *buffer[2][MAX_BUFFER];
char string_buffer[MAX_BUFFER];
bst *BST_NULL;

heap *new_heap_node(void *n, double key) {
    heap *h = (heap *) malloc(sizeof(heap));
    heap_count ++;
    h->n = n;
    h->key = key;
    h->head = NULL;
    h->next = h->prev = NULL;
    return h;
}

void free_heap_node(heap *h) {
    free(h);
    heap_count --;
}

heap *heap_merge(heap *h0, heap *h1) {
    if (h0 == NULL) 
        return h1;
    if (h1 == NULL) 
        return h0;
    if (h0->key < h1->key) {
        h1->next = h0->head;
        if (h0->head != NULL) 
            h0->head->prev = h1;
        h0->head = h1;
        h1->prev = h0;
        return h0;
    }
    else {
        h0->next = h1->head;
        if (h1->head != NULL) 
            h1->head->prev = h0;
        h1->head = h0;
        h0->prev = h1;
        return h1;
    }
}

heap *extract_min(heap *h) {
    heap *p = h->head, *q;
    free_heap_node(h);
    if (p == NULL) return NULL;
    heap **queue = (heap **) buffer[0];
    heap **stack = (heap **) buffer[1];
    int head = 0, tail = 0, top;
    while (p != NULL) {
        queue[tail ++] = p;
        p = p->next;
        q = queue[tail - 1];
        q->prev = q->next = NULL;
    }
    while (tail > 1) {
        for (top = 0; head < tail; ) {
            p = queue[head ++];
            q = queue[head ++];
            if (head == tail + 1) q = NULL;
            stack[top ++] = heap_merge(p, q);
        }
        head = tail = 0;
        while (top > 0) 
            queue[tail ++] = stack[-- top];
    }
    return queue[0];
}

heap *decrease_key(heap *h0, heap *h1, double key) {
    assert(key < h1->key);
    if (h1->prev == NULL) {
        assert(h0 == h1);
        h0->key = key;
        return h0;
    }
    else {
        if (h1->prev->next == h1) {
            h1->prev->next = h1->next;
            if (h1->next != NULL) 
                h1->next->prev = h1->prev;
        }
        else {
            assert(h1->prev->head == h1);
            h1->prev->head = h1->next;
            if (h1->next != NULL) 
                h1->next->prev = h1->prev;
        }
        h1->prev = h1->next = NULL;
        h1->key = key;
        return heap_merge(h0, h1);
    }
}

bst *new_bst_node(edge *e) {
    bst *b = (bst *) malloc(sizeof(bst));
    bst_count ++;
    b->e = e;
    b->left = b->right = BST_NULL;
    b->h = 0;
    b->s = 1;
    return b;
}

void free_bst_node(bst *b) {
    free(b);
    bst_count --;
}

void init_bst() {
    bst_count = 0;
    BST_NULL = new_bst_node(NULL);
    BST_NULL->left = BST_NULL->right = BST_NULL;
    BST_NULL->h = -1;
    BST_NULL->s = 0;
}

bst *new_bst() {
    return BST_NULL;
}

void traverse_bst(bst *b, bst **queue, int *tail) {
    if (b == BST_NULL) 
        return ;
    traverse_bst(b->left, queue, tail);
    queue[(*tail) ++] = b;
    traverse_bst(b->right, queue, tail);
}

void free_bst(bst *b) {
    if (b == BST_NULL) 
        return ;
    free_bst(b->left);
    free_bst(b->right);
    free_bst_node(b);
}

void update(bst *b) {
    b->s = b->left->s + b->right->s + 1;
    if (b->left->h > b->right->h)
        b->h = b->left->h + 1;
    else
        b->h = b->right->h + 1;
}

bst *rotate_right(bst *b) {
    bst *temp = b->left;
    b->left = temp->right;
    temp->right = b;
    update(b); update(temp);
    return temp;
}

bst *rotate_left(bst *b) {
    bst *temp = b->right;
    b->right = temp->left;
    temp->left = b;
    update(b); update(temp);
    return temp;
}

bst *re_balance(bst *b) {
    if (b->left->h > b->right->h + 1) {
        if (b->left->left->h >= b->left->right->h)
            b = rotate_right(b);
        else {
            b->left = rotate_left(b->left);
            b = rotate_right(b);
        }
    }
    if (b->right->h > b->left->h + 1) {
        if (b->right->right->h >= b->right->left->h)
            b = rotate_left(b);
        else {
            b->right = rotate_right(b->right);
            b = rotate_left(b);
        }
    }
    return b;
}

bst *bst_insert(bst *b, edge *e) {
    if (b == BST_NULL) {
        bst *temp = new_bst_node(e);
        return temp;
    }
    assert(strcmp(e->name, b->e->name) != 0);
    if (strcmp(e->name, b->e->name) == -1)
        b->left = bst_insert(b->left, e);
    else
        b->right = bst_insert(b->right, e);
    update(b);
    b = re_balance(b);
    return b;
}

bst *bst_search(bst *b, edge *e) {
    if (b == BST_NULL) 
        return NULL;
    if (strcmp(e->name, b->e->name) == 0) 
        return b;
    if (strcmp(e->name, b->e->name) == -1) 
        return bst_search(b->left, e);
    else 
        return bst_search(b->right, e);
}

void bst_trav(FILE *fout, bst *b) {
    if (b == BST_NULL) 
        return ;
    bst_trav(fout, b->left);
    fprintf(fout, "%s\n", b->e->name);
    bst_trav(fout, b->right);
}

list *new_list_node(edge *e) {
    list_count ++;
    list *p = (list *) malloc(sizeof(list));
    p->e = e;
    p->next = NULL;
    return p;
}

void free_list_node(list *p) {
    list_count --;
    free(p);
}

void free_list(list *p) {
    list *it = p, *pre = NULL;
    while (it != NULL) {
        pre = it;
        it = it->next;
        if (pre != NULL) {
            free_list_node(pre);
        }
    }
}

list *list_insert(list *p, edge *e) {
    list *new = new_list_node(e);
    new->next = p;
    return new;
}

list *list_merge(list *p, list *q) {
    list *temp = NULL, *last = NULL, *it = q;
    while (it != NULL) {
        if (temp != NULL) {
            temp = list_insert(temp, it->e);
        }
        else {
            temp = list_insert(temp, it->e);
            last = temp;
        }
        it = it->next;
    }
    if (last == NULL) {
        return p;
    }
    else {
        last->next = p;
        return temp;
    }
}

quad *new_quad_node(quad *f, int i) {
    quad *q = (quad *) malloc(sizeof(quad));
    quad_count ++;
    if (f == NULL) {
        q->A.x = q->A.y = 0;
        q->B.x = q->B.y = WIDTH;
    }
    else {
        point A = f->A, B = f->B, M;
        M.x = (f->A.x + f->B.x) / 2;
        M.y = (f->A.y + f->B.y) / 2;
        switch (i) {
            case NW: 
                q->A.x = A.x; q->A.y = M.y;
                q->B.x = M.x; q->B.y = B.y;
                break;
            case NE: 
                q->A.x = M.x; q->A.y = M.y;
                q->B.x = B.x; q->B.y = B.y;
                break;
            case SW: 
                q->A.x = A.x; q->A.y = A.y;
                q->B.x = M.x; q->B.y = M.y;
                break;
            case SE: 
                q->A.x = M.x; q->A.y = A.y;
                q->B.x = B.x; q->B.y = M.y;
                break;
        }
    }
    for (i = 0; i < 4; i ++) 
        q->child[i] = NULL;
    q->edges = NULL;
    return q;
}

void free_quad_node(quad *q) {
    quad_count --;
    free_list(q->edges);
    free(q);
}

int type_of(quad *q) {
    if (q->child[0] != NULL) return GRAY;
    if (q->edges != NULL) return BLACK;
    return WHITE;
}

void free_quad(quad *q) {
    if (type_of(q) == WHITE || type_of(q) == BLACK) {
        free_quad_node(q);
    }
    else {
        int i;
        for (i = 0; i < 4; i ++) {
            free_quad(q->child[i]);
        }
        free_quad_node(q);
    }
}

int sgn(double x) {
    if (ABS(x) < EPS) return 0;
    if (x < 0) return -1;
    return 1;
}

int quad_contain(quad *q, point *p) {
    if (q->A.x > p->x + EPS || q->B.x < p->x - EPS) return 0;
    if (q->A.y > p->y + EPS || q->B.y < p->y - EPS) return 0;
    return 1;
}

int window_contain(point *A, point *B, point *p) {
    if (A->x > p->x + EPS || B->x < p->x - EPS) return 0;
    if (A->y > p->y + EPS || B->y < p->y - EPS) return 0;
    return 1;
}

int window_contain_edge(point *A, point *B, edge *e) {
    if (! window_contain(A, B, e->a)) return 0;
    if (! window_contain(A, B, e->b)) return 0;
    return 1;
}

int quad_window_intersect(quad *q, point *A, point *B) {
    double LX = MAX(q->A.x, A->x), RX = MIN(q->B.x, B->x);
    int dx = sgn(RX - LX);
    double LY = MAX(q->A.y, A->y), RY = MIN(q->B.y, B->y);
    int dy = sgn(RY - LY);
    if (dy >= 0 && dx >= 0) 
        return INTERSECT;
    else 
        return SEPARATE;
}

double cross(point *a, point *b, point *c) {
    return (b->x - a->x) * (c->y - a->y) - (c->x - a->x) * (b->y - a->y);
}

void print_edge(edge *e) {
    if (e == NULL) 
        printf("null, ");
    else 
        printf("%s [%lf %lf] %s [%lf %lf], ", 
        e->a->name, e->a->x, e->a->y, e->b->name, e->b->x, e->b->y);
}

int edges_intersect(edge *e0, edge *e1) {
    int d[2][2];
    d[0][0] = sgn(cross(e0->a, e0->b, e1->a));
    d[0][1] = sgn(cross(e0->a, e0->b, e1->b));
    d[1][0] = sgn(cross(e1->a, e1->b, e0->a));
    d[1][1] = sgn(cross(e1->a, e1->b, e0->b));
    if (d[0][0] == 0 && d[0][1] == 0) {
        double dx = ABS(e0->a->x - e0->b->x);
        double dy = ABS(e0->a->y - e0->b->y);
        double x0, x1, x2, x3;
        if (dx > dy) {
            x0 = e0->a->x;
            x1 = e0->b->x;
            x2 = e1->a->x;
            x3 = e1->b->x;
        }
        else {
            x0 = e0->a->y;
            x1 = e0->b->y;
            x2 = e1->a->y;
            x3 = e1->b->y;
        }
        if (x0 > x1) {
            double temp = x0;
            x0 = x1;
            x1 = temp;
        }
        if (x2 > x3) {
            double temp = x2;
            x2 = x3;
            x3 = temp;
        }
        double L = MAX(x0, x2), R = MIN(x1, x3);
        int delta = sgn(R - L);
        switch (delta) {
            case 0: return TOUCHING;
            case 1: return INTERSECT;
            case -1: return SEPARATE;
        }
    }
    else if (d[0][0] == 0) {
        double dx = ABS(e0->a->x - e0->b->x);
        double dy = ABS(e0->a->y - e0->b->y);
        double x0, x1, x2, x3;
        if (dx > dy) {
            x0 = e0->a->x;
            x1 = e0->b->x;
            x2 = e1->a->x;
            x3 = e1->b->x;
        }
        else {
            x0 = e0->a->y;
            x1 = e0->b->y;
            x2 = e1->a->y;
            x3 = e1->b->y;
        }
        if (x0 > x1) {
            double temp = x0;
            x0 = x1;
            x1 = temp;
        }
        if (sgn(x0 - x2) == 0 || sgn(x1 - x2) == 0) 
            return TOUCHING;
        if (x0 < x2 && x2 < x1) 
            return INTERSECT;
        return SEPARATE;
    }
    else if (d[0][1] == 0) {
        double dx = ABS(e0->a->x - e0->b->x);
        double dy = ABS(e0->a->y - e0->b->y);
        double x0, x1, x2, x3;
        if (dx > dy) {
            x0 = e0->a->x;
            x1 = e0->b->x;
            x2 = e1->a->x;
            x3 = e1->b->x;
        }
        else {
            x0 = e0->a->y;
            x1 = e0->b->y;
            x2 = e1->a->y;
            x3 = e1->b->y;
        }
        if (x0 > x1) {
            double temp = x0;
            x0 = x1;
            x1 = temp;
        }
        if (sgn(x0 - x3) == 0 || sgn(x1 - x3) == 0) 
            return TOUCHING;
        if (x0 < x3 && x3 < x1) 
            return INTERSECT;
        return SEPARATE;
    }
    else if (d[1][0] == 0) {
        double dx = ABS(e1->a->x - e1->b->x);
        double dy = ABS(e1->a->y - e1->b->y);
        double x0, x1, x2, x3;
        if (dx > dy) {
            x0 = e0->a->x;
            x1 = e0->b->x;
            x2 = e1->a->x;
            x3 = e1->b->x;
        }
        else {
            x0 = e0->a->y;
            x1 = e0->b->y;
            x2 = e1->a->y;
            x3 = e1->b->y;
        }
        if (x2 > x3) {
            double temp = x2;
            x2 = x3;
            x3 = temp;
        }
        if (sgn(x2 - x0) == 0 || sgn(x3 - x0) == 0) 
            return TOUCHING;
        if (x2 < x0 && x0 < x3) 
            return INTERSECT;
        return SEPARATE;
    }
    else if (d[1][1] == 0) {
        double dx = ABS(e1->a->x - e1->b->x);
        double dy = ABS(e1->a->y - e1->b->y);
        double x0, x1, x2, x3;
        if (dx > dy) {
            x0 = e0->a->x;
            x1 = e0->b->x;
            x2 = e1->a->x;
            x3 = e1->b->x;
        }
        else {
            x0 = e0->a->y;
            x1 = e0->b->y;
            x2 = e1->a->y;
            x3 = e1->b->y;
        }
        if (x2 > x3) {
            double temp = x2;
            x2 = x3;
            x3 = temp;
        }
        if (sgn(x2 - x1) == 0 || sgn(x3 - x1) == 0) 
            return TOUCHING;
        if (x2 < x1 && x1 < x3) 
            return INTERSECT;
        return SEPARATE;
    }
    else {
        if (d[0][0] * d[0][1] < 0 && d[1][0] * d[1][1] < 0) 
            return INTERSECT;
        else 
            return SEPARATE;
    }
}

int edges_intersect_2(edge *e0, edge *e1) {
    int d[2][2];
    d[0][0] = sgn(cross(e0->a, e0->b, e1->a));
    d[0][1] = sgn(cross(e0->a, e0->b, e1->b));
    d[1][0] = sgn(cross(e1->a, e1->b, e0->a));
    d[1][1] = sgn(cross(e1->a, e1->b, e0->b));
    if (d[0][0] == 0 && d[0][1] == 0) {
        double dx = ABS(e0->a->x - e0->b->x);
        double dy = ABS(e0->a->y - e0->b->y);
        double x0, x1, x2, x3;
        if (dx > dy) {
            x0 = e0->a->x;
            x1 = e0->b->x;
            x2 = e1->a->x;
            x3 = e1->b->x;
        }
        else {
            x0 = e0->a->y;
            x1 = e0->b->y;
            x2 = e1->a->y;
            x3 = e1->b->y;
        }
        if (x0 > x1) {
            double temp = x0;
            x0 = x1;
            x1 = temp;
        }
        if (x2 > x3) {
            double temp = x2;
            x2 = x3;
            x3 = temp;
        }
        double L = MAX(x0, x2), R = MIN(x1, x3);
        int delta = sgn(R - L);
        switch (delta) {
            case 0: return TOUCHING;
            case 1: return INTERSECT;
            case -1: return SEPARATE;
        }
    }
    else if (d[0][0] == 0) {
        double dx = ABS(e0->a->x - e0->b->x);
        double dy = ABS(e0->a->y - e0->b->y);
        double x0, x1, x2, x3;
        if (dx > dy) {
            x0 = e0->a->x;
            x1 = e0->b->x;
            x2 = e1->a->x;
            x3 = e1->b->x;
        }
        else {
            x0 = e0->a->y;
            x1 = e0->b->y;
            x2 = e1->a->y;
            x3 = e1->b->y;
        }
        if (x0 > x1) {
            double temp = x0;
            x0 = x1;
            x1 = temp;
        }
        if (sgn(x0 - x2) == 0 || sgn(x1 - x2) == 0) 
            return TOUCHING;
        if (x0 < x2 && x2 < x1) 
            return TOUCHING;
        return SEPARATE;
    }
    else if (d[0][1] == 0) {
        double dx = ABS(e0->a->x - e0->b->x);
        double dy = ABS(e0->a->y - e0->b->y);
        double x0, x1, x2, x3;
        if (dx > dy) {
            x0 = e0->a->x;
            x1 = e0->b->x;
            x2 = e1->a->x;
            x3 = e1->b->x;
        }
        else {
            x0 = e0->a->y;
            x1 = e0->b->y;
            x2 = e1->a->y;
            x3 = e1->b->y;
        }
        if (x0 > x1) {
            double temp = x0;
            x0 = x1;
            x1 = temp;
        }
        if (sgn(x0 - x3) == 0 || sgn(x1 - x3) == 0) 
            return TOUCHING;
        if (x0 < x3 && x3 < x1) 
            return TOUCHING;
        return SEPARATE;
    }
    else if (d[1][0] == 0) {
        double dx = ABS(e1->a->x - e1->b->x);
        double dy = ABS(e1->a->y - e1->b->y);
        double x0, x1, x2, x3;
        if (dx > dy) {
            x0 = e0->a->x;
            x1 = e0->b->x;
            x2 = e1->a->x;
            x3 = e1->b->x;
        }
        else {
            x0 = e0->a->y;
            x1 = e0->b->y;
            x2 = e1->a->y;
            x3 = e1->b->y;
        }
        if (x2 > x3) {
            double temp = x2;
            x2 = x3;
            x3 = temp;
        }
        if (sgn(x2 - x0) == 0 || sgn(x3 - x0) == 0) 
            return TOUCHING;
        if (x2 < x0 && x0 < x3) 
            return TOUCHING;
        return SEPARATE;
    }
    else if (d[1][1] == 0) {
        double dx = ABS(e1->a->x - e1->b->x);
        double dy = ABS(e1->a->y - e1->b->y);
        double x0, x1, x2, x3;
        if (dx > dy) {
            x0 = e0->a->x;
            x1 = e0->b->x;
            x2 = e1->a->x;
            x3 = e1->b->x;
        }
        else {
            x0 = e0->a->y;
            x1 = e0->b->y;
            x2 = e1->a->y;
            x3 = e1->b->y;
        }
        if (x2 > x3) {
            double temp = x2;
            x2 = x3;
            x3 = temp;
        }
        if (sgn(x2 - x1) == 0 || sgn(x3 - x1) == 0) 
            return TOUCHING;
        if (x2 < x1 && x1 < x3) 
            return TOUCHING;
        return SEPARATE;
    }
    else {
        if (d[0][0] * d[0][1] < 0 && d[1][0] * d[1][1] < 0) 
            return INTERSECT;
        else 
            return SEPARATE;
    }
}

int quad_edge_intersect(quad *q, edge *e) {
    if (quad_contain(q, e->a) || quad_contain(q, e->b)) 
        return INTERSECT;
    point p[4]; edge e_[4];
    p[0] = q->A;
    p[1].x = q->B.x; p[1].y = q->A.y;
    p[2] = q->B;
    p[3].x = q->A.x; p[3].y = q->B.y;
    int i;
    for (i = 0; i < 4; i ++) {
        e_[i].a = p + i;
        e_[i].b = p + ((i + 1) % 4);
        if (edges_intersect(e, e_ + i) != SEPARATE) 
            return INTERSECT; 
    }
    return SEPARATE;
}

int window_edge_intersect(point *A, point *B, edge *e) {
    if (window_contain(A, B, e->a) || window_contain(A, B, e->b)) 
        return INTERSECT;
    point p[4]; edge e_[4];
    p[0] = *A;
    p[1].x = B->x; p[1].y = A->y;
    p[2] = *B;
    p[3].x = A->x; p[3].y = B->y;
    int i;
    for (i = 0; i < 4; i ++) {
        e_[i].a = p + i;
        e_[i].b = p + ((i + 1) % 4);
        if (edges_intersect(e, e_ + i) != SEPARATE) {
            return INTERSECT;
        }
    }
    return SEPARATE;
}

int valid(quad *q) {
    int count = 0;
    list *it;
    point *temp;
    switch (PM_TYPE) {
        case 1:
            it = q->edges;
            temp = NULL;
            while (it != NULL) {
                edge *e = it->e;
                if (quad_contain(q, e->a)) {
                    if (temp == NULL) 
                        temp = e->a;
                    else if (temp != e->a) 
                        return 0;
                }
                if (quad_contain(q, e->b)) {
                    if (temp == NULL) 
                        temp = e->b;
                    else if (temp != e->b) 
                        return 0;
                }
                it = it->next;
            }
            it = q->edges;
            if (it == NULL) {
                return 1;
            }
            else if (quad_contain(q, it->e->a)) {
                temp = it->e->a;
                while (it != NULL) {
                    if (it->e->a != temp && it->e->b != temp) 
                        return 0;
                    it = it->next;
                }
                return 1;
            }
            else if (quad_contain(q, it->e->b)) {
                temp = it->e->b;
                while (it != NULL) {
                    if (it->e->a != temp && it->e->b != temp) 
                        return 0;
                    it = it->next;
                }
                return 1;
            }
            else {
                if (it->next == NULL) 
                    return 1;
                else 
                    return 0;
            }
            break;
        case 2:
            it = q->edges;
            temp = NULL;
            while (it != NULL) {
                edge *e = it->e;
                if (quad_contain(q, e->a)) {
                    if (temp == NULL) 
                        temp = e->a;
                    else if (temp != e->a) 
                        return 0;
                } 
                if (quad_contain(q, e->b)) {
                    if (temp == NULL) 
                        temp = e->b;
                    else if (temp != e->b) 
                        return 0;
                }
                it = it->next;
            }
            it = q->edges;
            if (it == NULL) return 1;
            temp = it->e->a;
            while (it != NULL) {
                if (it->e->a != temp && it->e->b != temp) 
                    break;
                it = it->next;
            }
            if (it == NULL) {
                return 1;
            }
            else {
                it = q->edges;
                temp = it->e->b;
                while (it != NULL) {
                    if (it->e->a != temp && it->e->b != temp) 
                        return 0;
                    it = it->next;
                }
                return 1;
            }
            break;
        case 3: 
            it = q->edges;
            temp = NULL;
            while (it != NULL) {
                edge *e = it->e;
                if (quad_contain(q, e->a)) {
                    if (temp == NULL) 
                        temp = e->a;
                    else if (temp != e->a) 
                        return 0;
                } 
                if (quad_contain(q, e->b)) {
                    if (temp == NULL) 
                        temp = e->b;
                    else if (temp != e->b) 
                        return 0;
                }
                it = it->next;
            }
            return 1;
            break;
    }
}

void print_quad(quad *q, const char *from) {
    printf("%lf %lf %lf %lf %d ", q->A.x, q->A.y, q->B.x, q->B.y, type_of(q));
    list *temp = q->edges;
    while (temp != NULL) {
        printf("%s ", temp->e->name);
        temp = temp->next;
    }
    printf("%s\n", from);
}

void quad_insert(quad *q, list *edges, int depth) {
    if (type_of(q) == WHITE || type_of(q) == BLACK) {
        q->edges = list_merge(q->edges, edges);
        if (depth < MAX_DEPTH && ! valid(q)) {
            int i;
            for (i = 0; i < 4; i ++) {
                q->child[i] = new_quad_node(q, i);
                list *it = q->edges, *temp = NULL;
                while (it != NULL) {
                    edge *e = it->e;
                    if (quad_edge_intersect(q->child[i], e) == INTERSECT) {
                        temp = list_insert(temp, e);
                    }
                    it = it->next;
                }
                if (temp != NULL) {
                    quad_insert(q->child[i], temp, depth + 1);
                    free_list(temp);
                }
            }
            free_list(q->edges);
            q->edges = NULL;
        }
    }
    else {
        int i;
        for (i = 0; i < 4; i ++) {
            list *it = edges, *temp = NULL;
            while (it != NULL) {
                edge *e = it->e;
                if (quad_edge_intersect(q->child[i], e) == INTERSECT) {
                    temp = list_insert(temp, e);
                }
                it = it->next;
            }
            if (temp != NULL) {
                quad_insert(q->child[i], temp, depth + 1);
                free_list(temp);
            }
        }
    }
}

quad *quad_merge(quad *q) {
    int i, flag;
    quad *temp;
    switch (PM_TYPE) {
        case 1:
            flag = 0;
            for (i = 0; i < 4; i ++) {
                if (type_of(q->child[i]) != GRAY) 
                    flag = 1;
            }
            if (flag == 0) {
                return q;
            }
            else {
                for (i = 0; i < 4; i ++) {
                    if (type_of(q->child[i]) == GRAY) 
                        q->child[i] = quad_merge(q->child[i]);
                }
            }
        case 2:
        case 3:
            for (i = 0; i < 4; i ++) {
                if (type_of(q->child[i]) == GRAY) {
                    return q;
                }
            }
            temp = new_quad_node(NULL, -1);
            temp->A = q->A; temp->B = q->B;
            for (i = 0; i < 4; i ++) {
                list *it = q->child[i]->edges;
                while (it != NULL) {
                    edge *e = it->e;
                    list *it_ = temp->edges;
                    while (it_ != NULL) {
                        if (it_->e == e) break;
                        it_ = it_->next;
                    }
                    if (it_ == NULL) {
                        temp->edges = list_insert(temp->edges, e);
                    }
                    it = it->next;
                }
            }
            if (valid(temp)) {
                for (i = 0; i < 4; i ++) {
                    free_quad_node(q->child[i]);
                }
                free_quad_node(q);
                return temp;
            }
            else {
                free_quad_node(temp);
                return q;
            }
            break;
    }
}

quad *quad_delete(quad *q, edge *e) {
    if (type_of(q) == BLACK) {
        list *it = q->edges, *pre = NULL;
        while (it != NULL) {
            if (it->e == e) break;
            pre = it;
            it = it->next;
        }
        if (it != NULL) {
            if (pre == NULL) 
                q->edges = it->next;
            else 
                pre->next = it->next;
            free_list_node(it);
        }
        return q;
    }
    else if (type_of(q) == GRAY) {
        int i;
        for (i = 0; i < 4; i ++) {
            if (quad_edge_intersect(q->child[i], e) == INTERSECT) {
                q->child[i] = quad_delete(q->child[i], e);
            }
        }
        return quad_merge(q);
    }
    else {
        return q;
    }
}

list *quad_search(quad *q, point *p) {
    if (type_of(q) == BLACK) {
        list *it = q->edges, *temp = NULL;
        while (it != NULL) {
            edge *e = it->e;
            if (e->a == p || e->b == p) {
                temp = list_insert(temp, e);
            }
            it = it->next;
        }
        return temp;
    }
    else if (type_of(q) == GRAY) {
        int i;
        for (i = 0; i < 4; i ++) {
            if (quad_contain(q->child[i], p)) {
                return quad_search(q->child[i], p);
            }
        }
    }
    return NULL;
}

quad *quad_delete_point(quad *root, point *p) {
    list *temp = quad_search(root, p), *it = temp;
    while (it != NULL) {
        edge *e = it->e;
        assert(e->deleted == 0);
        root = quad_delete(root, e);
        e->deleted = 1;
        it = it->next;
    }
    if (temp != NULL)
        free_list(temp);
    return root;
}

void quad_search_window_2(quad *q, point *A, point *B, bst **ret) {
    if (type_of(q) == BLACK) {
        list *it = q->edges;
        while (it != NULL) {
            edge *e = it->e;
            if (window_edge_intersect(A, B, e) == INTERSECT) {
                if (bst_search(*ret, e) == NULL)
                    *ret = bst_insert(*ret, e);
            }
            it = it->next;
        }
    }
    else if (type_of(q) == GRAY) {
        int i;
        for (i = 0; i < 4; i ++) {
            if (quad_window_intersect(q->child[i], A, B) == INTERSECT) {
                quad_search_window_2(q->child[i], A, B, ret);
            }
        }
    }
}

void quad_search_window(quad *q, point *A, point *B, bst **ret) {
    if (type_of(q) == BLACK) {
        list *it = q->edges;
        while (it != NULL) {
            edge *e = it->e;
            if (window_contain_edge(A, B, e)) {
                if (bst_search(*ret, e) == NULL)
                    *ret = bst_insert(*ret, e);
            }
            it = it->next;
        }
    }
    else if (type_of(q) == GRAY) {
        int i;
        for (i = 0; i < 4; i ++) {
            if (quad_window_intersect(q->child[i], A, B) == INTERSECT) {
                quad_search_window(q->child[i], A, B, ret);
            }
        }
    }
}

void quad_search_edge(quad *q, edge *e, bst **ret) {
    if (type_of(q) == BLACK) {
        list *it = q->edges;
        while (it != NULL) {
            edge *e_ = it->e;
            if (edges_intersect(e, e_) != SEPARATE) {
                if (bst_search(*ret, e_) == NULL)
                    *ret = bst_insert(*ret, e_);
            }
            it = it->next;
        }
    }
    else if (type_of(q) == GRAY) {
        int i;
        for (i = 0; i < 4; i ++) {
            if (quad_edge_intersect(q->child[i], e) == INTERSECT) {
                quad_search_edge(q->child[i], e, ret);
            }
        }
    }
}

double dist2_points(point *a, point *b) {
    return (a->x - b->x) * (a->x - b->x) + (a->y - b->y) * (a->y - b->y);
}

double dist2_edge_point(edge *e, point *p) {
    double u = ((p->x - e->a->x) * (e->b->x - e->a->x)
            + (p->y - e->a->y) * (e->b->y - e->a->y))
        / dist2_points(e->a, e->b);
    if (0 <= u && u <= 1) {
        point t;
        t.x = e->a->x + u * (e->b->x - e->a->x);
        t.y = e->a->y + u * (e->b->y - e->a->y);
        return dist2_points(& t, p);
    }
    else {
        double da = dist2_points(e->a, p);
        double db = dist2_points(e->b, p);
        return MIN(da, db);
    }
}

double dist2_quad_point(quad *q, point *p) {
    if (quad_contain(q, p)) return 0;
    point p_[4]; edge e_[4];
    p_[0] = q->A;
    p_[1].x = q->B.x; p_[1].y = q->A.y;
    p_[2] = q->B;
    p_[3].x = q->A.x; p_[3].y = q->B.y;
    double ret = -1;
    int i;
    for (i = 0; i < 4; i ++) {
        e_[i].a = p_ + i;
        e_[i].b = p_ + ((i + 1) % 4);
        double d2 = dist2_edge_point(e_ + i, p);
        if (ret < 0 || d2 < ret) ret = d2;
    }
    return ret;
}

void quad_nearest(quad *q, point *p, edge **ret) {
    if (type_of(q) == BLACK) {
        list *it = q->edges;
        while (it != NULL) {
            edge *e = it->e;
            double d2 = dist2_edge_point(e, p);
            if (*ret == NULL || d2 < dist2_edge_point(*ret, p)) 
                *ret = e;
            it = it->next;
        }
    }
    else if (type_of(q) == GRAY) {
        int i;
        for (i = 0; i < 4; i ++) {
            double d2 = dist2_quad_point(q->child[i], p);
            if (*ret == NULL || d2 < dist2_edge_point(*ret, p)) 
                quad_nearest(q->child[i], p, ret);
        }
    }
}

void quad_k_nearest(quad *q, point *p, edge **ret, int k) {
    if (type_of(q) == BLACK) {
        list *it = q->edges;
        while (it != NULL) {
            edge *e = it->e;
            double d2 = dist2_edge_point(e, p);
            int i, j;
            for (i = 0; i < k; i ++) {
                if (ret[i] == e) break;
            }
            if (i == k) {
                for (i = 0; i < k; i ++) {
                    if (ret[i] == NULL || dist2_edge_point(ret[i], p) > d2) 
                        break;
                }
                if (i < k) {
                    for (j = k - 1; j > i; j --) {
                        ret[j] = ret[j - 1];
                    }
                    ret[i] = e;
                }
            }
            it = it->next;
        }
    }
    else if (type_of(q) == GRAY) {
        int i;
        for (i = 0; i < 4; i ++) {
            double d2 = dist2_quad_point(q->child[i], p);
            if (ret[k - 1] == NULL || d2 < dist2_edge_point(ret[k - 1], p)) 
                quad_k_nearest(q->child[i], p, ret, k);
        }
    }
}

void quad_k_nearest_bfs(quad *root, point *p, edge **ret, int k) {
    heap *h = new_heap_node((void *) root, 0);
    while (h != NULL) {
        quad *q = (quad *) h->n;
        double d2 = h->key;
        h = extract_min(h);
        if (ret[k - 1] != NULL && d2 > dist2_edge_point(ret[k - 1], p)) {
            break;
        }
        else {
            if (type_of(q) == BLACK) {
                list *it = q->edges;
                while (it != NULL) {
                    edge *e = it->e;
                    double d2 = dist2_edge_point(e, p);
                    int i, j;
                    for (i = 0; i < k; i ++) {
                        if (ret[i] == e) break;
                    }
                    if (i == k) {
                        for (i = 0; i < k; i ++) {
                            if (ret[i] == NULL) break;
                            double d2_ = dist2_edge_point(ret[i], p);
                            int s = sgn(d2_ - d2);
                            if (s > 0 || (s == 0 
                            && strcmp(ret[i]->name, e->name) > 0)) 
                                break;
                        }
                        if (i < k) {
                            for (j = k - 1; j > i; j --) {
                                ret[j] = ret[j - 1];
                            }
                            ret[i] = e;
                        }
                    }
                    it = it->next;
                }
            }
            else if (type_of(q) == GRAY) {
                int i;
                for (i = 0; i < 4; i ++) {
                    double d2 = dist2_quad_point(q->child[i], p);
                    h = heap_merge(h, new_heap_node((void *) q->child[i], d2));
                }
            }
        }
    }
    while (h != NULL) 
        h = extract_min(h);
}

point gen_point();

int on(point *p, edge *e) {
    int d = sgn(cross(p, e->a, e->b));
    if (d == 0) {
        double dx = ABS(e->a->x - e->b->x);
        double dy = ABS(e->a->y - e->b->y);
        if (dx > dy) {
            if (sgn(p->x - e->a->x) == 0 || sgn(p->x - e->b->x) == 0) 
                return 1;
            if (sgn(p->x - e->a->x) == sgn(e->b->x - p->x)) 
                return 1;
        }
        else {
            if (sgn(p->y - e->a->y) == 0 || sgn(p->y - e->b->y) == 0) 
                return 1;
            if (sgn(p->y - e->a->y) == sgn(e->b->y - p->y)) 
                return 1;
        }
    }
    return 0;
}

int polygon_contain(point *a, int N, point *p) {
    int i;
    for (i = 0; i < N; i ++) {
        if (sgn(p->x - a[i].x) == 0 && sgn(p->y - a[i].y) == 0) 
            return 1;
        edge ei;
        ei.a = a + i;
        ei.b = a + (i + 1) % N;
        if (on(p, & ei)) 
            return 1;
    }
    int flag, count;
    do {
        point delta;
        do {
            delta = gen_point();
            delta.x -= WIDTH / 2;
            delta.y -= WIDTH / 2;
        } while (ABS(delta.x) < 0.5);
        delta.x *= (double) WIDTH / delta.x;
        delta.y *= (double) WIDTH / delta.x;
        point p_ = *p;
        while ((p_.x > -1 && p_.y > -1) && (p_.x < WIDTH + 1 && p_.y < WIDTH + 1)) {
            p_.x += delta.x;
            p_.y += delta.y;
        }
        edge e;
        e.a = p;
        e.b = & p_;
        flag = count = 0;
        for (i = 0; i < N; i ++) {
            edge ei;
            ei.a = a + i;
            ei.b = a + (i + 1) % N;
            int ret = edges_intersect_2(& e, & ei);
            if (ret == TOUCHING) {
                flag = 1;
                break;
            }
            else if (ret == INTERSECT) {
                count ++;
            }
        }
    } while (flag == 1);
    return count % 2 == 1;
}

double polygon_area(point *a, int N) {
    int i;
    double s = 0;
    for (i = 0; i < N; i ++) {
        s += cross(a, a + i, a + (i + 1) % N);
    }
    return ABS(s);
}

int polygon_intersect_edge(point *a, int N, edge *e) {
    if (polygon_contain(a, N, e->a) || polygon_contain(a, N, e->b)) return 1;
    int i;
    for (i = 0; i < N; i ++) {
        edge ei;
        ei.a = a + i;
        ei.b = a + (i + 1) % N;
        if (edges_intersect(e, & ei) != SEPARATE) 
            return 1;
    }
    return 0;
}

int polygon_intersect_quad(point *a, int N, quad *q) {
    point p_[4]; edge e_[4];
    p_[0] = q->A;
    p_[1].x = q->B.x; p_[1].y = q->A.y;
    p_[2] = q->B;
    p_[3].x = q->A.x; p_[3].y = q->B.y;
    int i, j;
    for (i = 0; i < N; i ++) {
        if (quad_contain(q, a + i)) 
            return 1;
    }
    for (i = 0; i < 4; i ++) {
        if (polygon_contain(a, N, p_ + i)) 
            return 1;
    }
    for (i = 0; i < 4; i ++) {
        e_[i].a = p_ + i;
        e_[i].b = p_ + ((i + 1) % 4);
        for (j = 0; j < N; j ++) {
            edge ej;
            ej.a = a + j;
            ej.b = a + (j + 1) % N;
            if (edges_intersect(& ej, e_ + i) != SEPARATE) 
                return 1;
        }
    }
    return 0;
}

void quad_search_polygon(quad *q, point *a, int N, bst **ret) {
    if (type_of(q) == BLACK) {
        list *it = q->edges;
        while (it != NULL) {
            edge *e_ = it->e;
            if (polygon_intersect_edge(a, N, e_)) {
                if (bst_search(*ret, e_) == NULL)
                    *ret = bst_insert(*ret, e_);
            }
            it = it->next;
        }
    }
    else if (type_of(q) == GRAY) {
        int i;
        for (i = 0; i < 4; i ++) {
            if (polygon_intersect_quad(a, N, q->child[i])) {
                quad_search_polygon(q->child[i], a, N, ret);
            }
        }
    }
}

void polygon_display(point *temp, int N, FILE *fout) {
    int i;
    for (i = 0; i < N; i ++) {
        fprintf(fout, "DL(%.2lf,%.2lf,%.2lf,%.2lf)\n", 
            temp[i].x, temp[i].y, 
            temp[(i + 1) % N].x, temp[(i + 1) % N].y);
    }
}

int dround(double x);

void window_display(point *A, point *B, FILE *fout);

int quad_point_location(quad *root, point *p, point **a, int *N, FILE *fout) {
    list *ret = NULL;
    *N = 0;
    int K = 20;
    edge **near = (edge **) malloc(sizeof(edge *) * K);
    int i, j;
    for (i = 0; i < K; i ++) 
        near[i] = NULL;
    quad_k_nearest_bfs(root, p, near, K);
    if (near[0] == NULL) {
        return 1;
    }
    else {
        if (on(p, near[0])) {
            //printf("on edge\n");
            return 2;
        }
        double d2 = dist2_edge_point(near[0], p);
        for (i = 1; i < K; i ++) {
            double d2_ = -1;
            if (near[i] != NULL)
                d2_ = dist2_edge_point(near[i], p);
            if (d2_ != d2) break;
        }
        j = i;
        if (j == K) {
            printf("max degree\n");
            return 3;
        }
        if (j == 1) {
            int d = sgn(cross(p, near[0]->a, near[0]->b));
            if (d == 0) {                
                printf("dangling edge\n");
                return 4;
            }
            else {
                point *start, *cur, *last;
                cur = near[0]->b;
                start = last = near[0]->a;
                ret = list_insert(ret, near[0]);
                (*N) ++;
                int k = 0;
                while (cur != start) {
                    list *temp = quad_search(root, cur);
                    point *next[3];
                    next[0] = next[1] = next[2] = NULL;
                    edge *next_[3];
                    list *it = temp;
                    while (it != NULL) {
                        edge *e = it->e;
                        point *other = e->a;
                        if (cur == e->a) other = e->b;
                        if (last != other) {
                            int type = sgn(cross(last, cur, other));
                            if (next[type + 1] == NULL 
                            || sgn(cross(cur, next[type + 1], other)) == d) {
                                next[type + 1] = other;
                                next_[type + 1] = e;
                            }
                        }
                        it = it->next;
                    }
                    free_list(temp);
                    edge *e;
                    last = cur;
                    if (d > 0) {
                        if (next[2] != NULL) {
                            cur = next[2];
                            e = next_[2];
                        }
                        else if (next[1] != NULL) {
                            cur = next[1];
                            e = next_[1];
                        }
                        else if (next[0] != NULL) {
                            cur = next[0];
                            e = next_[0];
                        }
                        else {
                            printf("dead end\n");
                            *N = 0;
                            free_list(ret);
                            return 5;
                        }
                    }
                    else {
                        if (next[0] != NULL) {
                            cur = next[0];
                            e = next_[0];
                        }
                        else if (next[1] != NULL) {
                            cur = next[1];
                            e = next_[1];
                        }
                        else if (next[2] != NULL) {
                            cur = next[2];
                            e = next_[2];
                        }
                        else {
                            printf("dead end\n");
                            *N = 0;
                            free_list(ret);
                            return 6;
                        }
                    }
                    it = ret;
                    while (it != NULL) {
                        if (it->e == e) {
                            printf("dead end\n");
                            *N = 0;
                            free_list(ret);
                            return 7;
                        }
                        it = it->next;
                    }
                    (*N) ++;
                    ret = list_insert(ret, e);
                }
            }
        }
        else {
            //printf("another case\n");
            for (i = 0; i < j; i ++) {
                if (near[i]->a != near[0]->a && near[i]->b != near[0]->a) 
                    break;
            }
            point *next[3][2];
            next[0][0] = next[1][0] = next[2][0] = NULL;
            next[0][1] = next[1][1] = next[2][1] = NULL;
            edge *next_[3][2];
            next_[0][0] = next_[1][0] = next_[2][0] = NULL;
            next_[0][1] = next_[1][1] = next_[2][1] = NULL;
            if (i == j) {
                for (i = 0; i < j; i ++) {
                    point *other;
                    if (near[i]->a == near[0]->a)
                        other = near[i]->b;
                    else 
                        other = near[i]->a;
                    int type = sgn(cross(p, near[0]->a, other));
                    if (next[type + 1][0] == NULL 
                    || sgn(cross(near[0]->a, next[type + 1][0], other)) == type) {
                        if (next[type + 1][0] != NULL) {
                            next[type + 1][1] = next[type + 1][0];
                            next_[type + 1][1] = next_[type + 1][0];
                        }
                        next[type + 1][0] = other;
                        next_[type + 1][0] = near[i];
                    }
                    else if (next[type + 1][1] == NULL 
                    || sgn(cross(near[0]->a, next[type + 1][1], other)) == type) {
                        next[type + 1][1] = other;
                        next_[type + 1][1] = near[i];
                    }
                }
            }
            else {
                for (i = 0; i < j; i ++) {
                    if (near[i]->a != near[0]->b && near[i]->b != near[0]->b) 
                        break;
                }
                if (i == j) {
                    for (i = 0; i < j; i ++) {
                        point *other;
                        if (near[i]->a == near[0]->b)
                            other = near[i]->b;
                        else 
                            other = near[i]->a;
                        int type = sgn(cross(p, near[0]->b, other));
                        if (next[type + 1][0] == NULL 
                        || sgn(cross(near[0]->b, next[type + 1][0], other)) == type) {
                            if (next[type + 1][0] != NULL) {
                                next[type + 1][1] = next[type + 1][0];
                                next_[type + 1][1] = next_[type + 1][0];
                            }
                            next[type + 1][0] = other;
                            next_[type + 1][0] = near[i];
                        }
                        else if (next[type + 1][1] == NULL 
                        || sgn(cross(near[0]->b, next[type + 1][1], other)) == type) {
                            next[type + 1][1] = other;
                            next_[type + 1][1] = near[i];
                        }
                    }
                }
                else {
                    printf("quad error\n");
                    return 8;
                }
            }
            if (next[1][1] != NULL) {
                
                print_edge(next_[1][1]);
                print_edge(next_[1][0]);
                printf("\n");
            }
            assert(next[1][1] == NULL);
            edge *e0 = next_[0][0];
            if (e0 == NULL) {
                if (next_[1][0] != NULL)
                    e0 = next_[1][0];
                else 
                    e0 = next_[2][1];
            }
            if (e0 == NULL) {
                printf("dangling edge\n");
                return 9;
            }
            else {
                int d = sgn(cross(p, e0->a, e0->b));
                point *start, *cur, *last;
                cur = e0->b;
                start = last = e0->a;
                ret = list_insert(ret, e0);
                (*N) ++;
                int k = 0;
                while (cur != start) {
                    list *temp = quad_search(root, cur);
                    point *next[3];
                    next[0] = next[1] = next[2] = NULL;
                    edge *next_[3];
                    next_[0] = next_[1] = next_[2] = NULL;
                    list *it = temp;
                    while (it != NULL) {
                        edge *e = it->e;
                        point *other = e->a;
                        if (cur == e->a) other = e->b;
                        if (last != other) {
                            int type = sgn(cross(last, cur, other));
                            if (next[type + 1] == NULL 
                            || sgn(cross(cur, next[type + 1], other)) == d) {
                                next[type + 1] = other;
                                next_[type + 1] = e;
                            }
                        }
                        it = it->next;
                    }
                    free_list(temp);
                    edge *e;
                    last = cur;
                    if (d > 0) {
                        if (next[2] != NULL) {
                            cur = next[2];
                            e = next_[2];
                        }
                        else if (next[1] != NULL) {
                            cur = next[1];
                            e = next_[1];
                        }
                        else if (next[0] != NULL) {
                            cur = next[0];
                            e = next_[0];
                        }
                        else {
                            printf("dead end\n");
                            *N = 0;
                            free_list(ret);
                            return 10;
                        }
                    }
                    else {
                        if (next[0] != NULL) {
                            cur = next[0];
                            e = next_[0];
                        }
                        else if (next[1] != NULL) {
                            cur = next[1];
                            e = next_[1];
                        }
                        else if (next[2] != NULL) {
                            cur = next[2];
                            e = next_[2];
                        }
                        else {
                            printf("dead end\n");
                            *N = 0;
                            free_list(ret);
                            return 11;
                        }
                    }
                    it = ret;
                    while (it != NULL) {
                        if (it->e == e) {
                            printf("dead end\n");
                            *N = 0;
                            free_list(ret);
                            return 12;
                        }
                        it = it->next;
                    }
                    (*N) ++;
                    ret = list_insert(ret, e);
                }
            }
        }
    }
    point *temp = (point *) malloc(sizeof(point) * (*N + 1));
    list *it = ret;
    i = 0;
    if (it->e->a == it->next->e->a || it->e->a == it->next->e->b) 
        temp[i ++] = *(it->e->b);
    else 
        temp[i ++] = *(it->e->a);
    while (it != NULL) {
        if (sgn(it->e->a->x - temp[i - 1].x) == 0 
        && sgn(it->e->a->y - temp[i - 1].y) == 0) 
            temp[i ++] = *(it->e->b);
        else 
            temp[i ++] = *(it->e->a);
        it = it->next;
    }
    free_list(ret);
    if (! polygon_contain(temp, *N, p)) {
        //printf("out %d\n", *N);
        fprintf(fout, "NO ENCLOSING POLYGON\n");
        if (DISPLAY && ALL_DISPLAY) {
            fprintf(fout, "$$$$ SP(%.2lf,%.2lf)\n", (double) WIDTH, (double) WIDTH);
            polygon_display(temp, *N, fout);
            fprintf(fout, "DD(%.2lf,%.2lf,%d)\n", p->x, p->y, DOT_RADIUS);
            fprintf(fout, "LD(%d,%d)\n", DASH_BLACK, DASH_WHITE);
            window_display(& root->A, & root->B, fout);
            fprintf(fout, "EP\n");
        }
        free(temp);
        *a = NULL;
        *N = 0;
    }
    else {
        //printf("in %d\n", *N);
        fprintf(fout, "POLYGON FOUND: %d/2 PIXELS\n", 
            dround(polygon_area(temp, *N)));
        if (DISPLAY && ALL_DISPLAY) {
            fprintf(fout, "$$$$ SP(%.2lf,%.2lf)\n", (double) WIDTH, (double) WIDTH);
            polygon_display(temp, *N, fout);
            fprintf(fout, "DD(%.2lf,%.2lf,%d)\n", p->x, p->y, DOT_RADIUS);
            fprintf(fout, "LD(%d,%d)\n", DASH_BLACK, DASH_WHITE);
            window_display(& root->A, & root->B, fout);
            fprintf(fout, "EP\n");
        }
        *a = temp;
    }
    return 0;
}

void quad_trav(quad *q, FILE *fout) {
    if (type_of(q) == WHITE) {
        fprintf(fout, "W");
    }
    else if (type_of(q) == BLACK) {
        fprintf(fout, "B[");
        list *it = q->edges;
        while (it != NULL) {
            edge *e = it->e;
            if (it->next == NULL) 
                fprintf(fout, "%s", e->name);
            else 
                fprintf(fout, "%s,", e->name);
            it = it->next;
        }
        fprintf(fout, "]");
    }
    else if (type_of(q) == GRAY) {
        int i;
        fprintf(fout, "G");
        for (i = 0; i < 4; i ++) {
            quad_trav(q->child[i], fout);
        }
    }
}

void quad_trav_2(quad *q, char *sout, int *N) {
    if (type_of(q) == WHITE) {
        *N += sprintf(sout + *N, "W");
    }
    else if (type_of(q) == BLACK) {
        *N += sprintf(sout + *N, "B[");
        list *it = q->edges;
        while (it != NULL) {
            edge *e = it->e;
            if (it->next == NULL) 
                *N += sprintf(sout + *N, "%s", e->name);
            else 
                *N += sprintf(sout + *N, "%s,", e->name);
            it = it->next;
        }
        *N += sprintf(sout + *N, "]");
    }
    else if (type_of(q) == GRAY) {
        int i;
        *N += sprintf(sout + *N, "G");
        for (i = 0; i < 4; i ++) {
            quad_trav_2(q->child[i], sout, N);
        }
    }
}

void quad_trav_3(quad *q, char *sout, int *N) {
    if (type_of(q) == WHITE) {
        *N += sprintf(sout + *N, "W");
    }
    else if (type_of(q) == BLACK) {
        *N += sprintf(sout + *N, "B[");
        list *it = q->edges;
        while (it != NULL) {
            edge *e = it->e;
            if (it->next == NULL) 
                *N += sprintf(sout + *N, "%s", e->name);
            else 
                *N += sprintf(sout + *N, "%s,", e->name);
            it = it->next;
        }
        *N += sprintf(sout + *N, "]");
    }
    else if (type_of(q) == GRAY) {
        int i;
        for (i = 0; i < 4; i ++) {
            quad_trav_3(q->child[i], sout, N);
        }
        *N += sprintf(sout + *N, "G");
    }
}

point gen_point() {
    point a;
    a.x = (rand() * (RAND_MAX + 1) + rand()) % WIDTH;
    a.y = (rand() * (RAND_MAX + 1) + rand()) % WIDTH;
    return a;
}

void gen_name(char *name, int i) {
    int j, k;
    if (i == 0) {
        name[0] = 'A';
        name[1] = '\0';
    }
    else {
        j = i;
        k = 0;
        while (j > 0) {
            name[k ++] = 'A' + j % 26;
            j = j / 26;
        }
        name[k] = '\0';
    }
}

point *gen_polygon(int N) {
    point *a = (point *) malloc(sizeof(point) * N);
    int i, j;
    for (i = 0; i < N; i ++) {
        do {
            a[i] = gen_point();
            for (j = 0; j < i; j ++) {
                if (sgn(a[j].x - a[i].x) == 0 && sgn(a[j].y - a[i].y) == 0) 
                    break;
            }
        } while (j < i);
    }
    int *perm = (int *) malloc(sizeof(int) * N);
    point *b = (point *) malloc(sizeof(point) * N);
    int flag;
    do {
        for (i = 0; i < N; i ++) {
            perm[i] = i;
        }
        for (i = N - 1; i >= 1; i --) {
            j = rand() % N;
            int temp = perm[i];
            perm[i] = perm[j];
            perm[j] = temp;
        }
        flag = 0;
        for (i = 0; i < N; i ++) {
            for (j = i + 2; j < N; j ++) {
                if (i == 0 && j == N - 1) continue;
                edge ei, ej;
                ei.a = a + perm[i];
                ei.b = a + perm[(i + 1) % N];
                ej.a = a + perm[j];
                ej.b = a + perm[(j + 1) % N];
                if (edges_intersect(& ei, & ej) == INTERSECT) {
                    flag = 1;
                    break;
                }
            }
        }
    } while (flag == 1);
    for (i = 0; i < N; i ++) {
        b[i] = a[perm[i]];
    }
    free(a);
    free(perm);
    return b;
}

void load_data(const char *file, point *a, int *N, edge *b, int *M) {
    FILE *fin = fopen(file, "r");
    char buffer[256];
    *N = *M = 0;
    while (fgets(buffer, 256, fin) != NULL) {
        point A, B;
        double x1, y1, x2, y2;
        sscanf(buffer, "Line[{{%lf, %lf}, {%lf, %lf}}]", & x1, & y1, & x2, & y2);
        A.x = x1; A.y = y1;
        B.x = x2; B.y = y2;
        int i, j;
        for (i = 0; i < *N; i ++) {
            if (sgn(a[i].x - A.x) == 0 && sgn(a[i].y - A.y) == 0) 
                break;
        }
        if (i == *N) {
            gen_name(A.name, i);
            //table[i] = NULL;
            a[(*N) ++] = A;
        }
        for (j = 0; j < *N; j ++) {
            if (sgn(a[j].x - B.x) == 0 && sgn(a[j].y - B.y) == 0) 
                break;
        }
        if (j == *N) {
            gen_name(B.name, j);
            //table[j] = NULL;
            a[(*N) ++] = B;
        }
        edge e;
        e.a = a + i;
        e.b = a + j;
        /*
        if (strcmp(e.a->name, e.b->name) == 1) {
            point *temp = e.a;
            e.a = e.b;
            e.b = temp;
        }
        */
        e.deleted = 1;
        e.name[0] = '\0';
        strcat(e.name, e.a->name);
        strcat(e.name, e.b->name);
        b[(*M) ++] = e;
        /*
        adj *node = (adj *) malloc(sizeof(adj));
        node->e = b + *M - 1;
        node->p = i;
        node->next = table[j];
        table[j] = node;
        node = (adj *) malloc(sizeof(adj));
        node->e = b + *M - 1;
        node->p = j;
        node->next = table[i];
        table[i] = node;
        */
        //printf("%s\n", b[*M - 1].name);
        //print_edge(& e);
    }
    
    int i, j;
    for (i = 0; i < *M; i ++) 
        for (j = i + 1; j < *M; j ++) {
            if (strcmp(b[i].name, b[j].name) == 0) {
                printf("%d %d\n", b[i].a - a, b[i].b - a);
                printf("%d %d\n", b[j].a - a, b[j].b - a);
                printf("%s %s\n", b[i].name, b[j].name);
            }
            assert(strcmp(b[i].name, b[j].name) != 0);
        }
    printf("load: %d %d\n", *N, *M);
    fclose(fin);
}

int dround(double x) {
    return (int) (x + 0.5);
}

void quad_display(quad *q, FILE *fout) {
    if (type_of(q) != GRAY) {
        return ;
    }
    else {
        double rx = (q->A.x + q->B.x) / 2;
        double ry = (q->A.y + q->B.y) / 2;
        fprintf(fout, "DL(%.2lf,%.2lf,%.2lf,%.2lf)\n", 
            q->A.x, ry, q->B.x, ry);
        fprintf(fout, "DL(%.2lf,%.2lf,%.2lf,%.2lf)\n", 
            rx, q->A.y, rx, q->B.y);
        int i;
        for (i = 0; i < 4; i ++) {
            quad_display(q->child[i], fout);
        }
    }
}

void edge_display(edge *e, FILE *fout) {
    fprintf(fout, "DL(%.2lf,%.2lf,%.2lf,%.2lf)\n", 
        e->a->x, e->a->y, e->b->x, e->b->y);
}

void window_display(point *A, point *B, FILE *fout) {
    fprintf(fout, "DL(%.2lf,%.2lf,%.2lf,%.2lf)\n", 
            A->x, A->y, A->x, B->y);
    fprintf(fout, "DL(%.2lf,%.2lf,%.2lf,%.2lf)\n", 
            A->x, B->y, B->x, B->y);
    fprintf(fout, "DL(%.2lf,%.2lf,%.2lf,%.2lf)\n", 
            B->x, B->y, B->x, A->y);
    fprintf(fout, "DL(%.2lf,%.2lf,%.2lf,%.2lf)\n", 
            B->x, A->y, A->x, A->y);
}

void display(quad *root, edge *b, int M, FILE *fout) {
    fprintf(fout, "$$$$ SP(%.2lf,%.2lf)\n", (double) WIDTH, (double) WIDTH);
    int j;
    for (j = 0; j < M; j ++) {
        if (! b[j].deleted) 
            edge_display(b + j, fout);
    }
    fprintf(fout, "LD(%d,%d)\n", DASH_BLACK, DASH_WHITE);
    window_display(& root->A, & root->B, fout);
    quad_display(root, fout);
    fprintf(fout, "EP\n");
}

void bst_display(bst *b, FILE *fout) {
    if (b == BST_NULL) 
        return ;
    bst_display(b->left, fout);
    edge_display(b->e, fout);
    bst_display(b->right, fout);
}

point *gen_points(int N) {
    point *a = (point *) malloc(sizeof(point) * N);
    int i, j, k;
    for (i = 0; i < N; i ++) {
        a[i] = gen_point();
        gen_name(a[i].name, i);
    }
    return a;
}

edge *gen_edges(point *a, int N, int *M) {
    edge *b = (edge *) malloc(sizeof(edge) * *M);
    int i, j;
    for (i = 0; i < *M; i ++) {
        edge e;
        int k = 0;
        do {
            int A = rand() % N, B = A;
            while (B == A) B = rand() % N;
            e.a = a + A;
            e.b = a + B;
            for (j = 0; j < i; j ++) {
                if (edges_intersect(& e, b + j) == INTERSECT) 
                    break;
            }
            if (++ k == N) {
                *M = i;
                return b;
            }
        } while (j != i);
        b[i].a = e.a;
        b[i].b = e.b;
        b[i].name[0] = '\0';
        strcat(b[i].name, e.a->name);
        strcat(b[i].name, e.b->name);
        b[i].deleted = 1;
    }
    return b;
}

quad *build_quad(char *buffer, int *N, bst *dict, quad *f, int i) {
    char cur = buffer[*N];
    if (cur == '\0') 
        return NULL;
    quad *q = new_quad_node(f, i);
    (*N) ++;
    if (cur == 'B') {
        char s[8], foo;
        *N += sscanf(buffer + *N, "%c", & foo);
        while (foo != ']') {
            int j = 0;
            while (buffer[*N] != ',' && buffer[*N] != ']') {
                *N += sscanf(buffer + *N, "%c", s + j);
                j ++;
            }
            s[j] = '\0';
            *N += sscanf(buffer + *N, "%c", & foo);
            edge e_;
            strcpy(e_.name, s);
            edge *e = bst_search(dict, & e_)->e;
            q->edges = list_insert(q->edges, e);
        }
    }
    else if (cur == 'G') {
        int j;
        for (j = 0; j < 4; j ++) {
            q->child[j] = build_quad(buffer, N, dict, q, j);
        }
    }
    return q;
}

void test_file(const char *file, 
    const char *input, const char *decode, const char *output, int O) {
    point *a = (point *) malloc(sizeof(point) * MAX_POINTS);
    edge *b = (edge *) malloc(sizeof(edge) * MAX_POINTS * 3);
    int N, M;
    load_data(file, a, & N, b, & M);
    FILE *fin = fopen(input, "w");
    FILE *fout = fopen(output, "w");
    FILE *fd = fopen(decode, "w");
    if (! STATIC) {
        fprintf(fin, "INIT_QUADTREE(%d)\n", MAX_DEPTH);
        fprintf(fd, "1 %d\n", MAX_DEPTH);
    }
    int i, j, k;
    bst *dict = new_bst();
    for (i = 0; i < M; i ++) {
        dict = bst_insert(dict, b + i);
        fprintf(fin, "CREATE_LINE(%s,%d,%d,%d,%d)\n", 
            b[i].name, dround(b[i].a->x), dround(b[i].a->y), 
            dround(b[i].b->x), dround(b[i].b->y));
        fprintf(fd, "4 %s %d %d %d %d\n", 
            b[i].name, dround(b[i].a->x), dround(b[i].a->y), 
            dround(b[i].b->x), dround(b[i].b->y));
        fprintf(fout, "LINE %s IS CREATED\n", b[i].name);
    }
    fprintf(fin, "LIST LINES()\n");
    fprintf(fd, "3\n");
    bst_trav(fout, dict);
    quad *root = new_quad_node(NULL, -1);
    int type[OP_TYPE];
    for (i = 0; i < OP_TYPE; i ++) 
        type[i] = 0;
    int lines = 0;
    for (i = 0; i < M; i ++) {
        if (! STATIC && rand() % 2 == 0) continue;
        if (b[i].deleted) {
            list *temp = new_list_node(b + i);
            quad_insert(root, temp, 0);
            free_list(temp);
            b[i].deleted = 0;
            if (! STATIC) {
                fprintf(fin, "INSERT(%s)\n", b[i].name);
                fprintf(fd, "6 %s\n", b[i].name);
                fprintf(fout, "%s IS INSERTED\n", b[i].name);
            }
        }
    }
    if (STATIC) {
        fprintf(fin, "BUILD_QUADTREE(%d)\n", MAX_DEPTH);
        quad_trav(root, fin); fprintf(fin, "\n");
    }
    int len = 0, cur = 0;
    quad_trav_2(root, string_buffer, & len);
    printf("%s\n", string_buffer);
    quad *root_ = build_quad(string_buffer, & cur, dict, NULL, -1);
    quad *temp = root;
    root = root_;
    free_quad(temp);
    /*
    len = 0;
    quad_trav_3(root, string_buffer, & len);
    printf("%s\n", string_buffer);
    */
    if (DISPLAY) {
        display(root, b, M, fout);
        fprintf(fin, "DISPLAY()\n");
        fprintf(fd, "2\n");
    }
    printf("init group done: %d %d\n", quad_count, list_count);
    for (i = 0; i < O; ) {
        int o = rand() % OP_TYPE;
        if (o != 1 && o != 2 && o != 6) continue;
        type[o] ++;
        //printf("%d\n", o);
        switch (o) {
            case 0: 
                {
                    if (STATIC) break;
                    if (DISPLAY) {
                        display(root, b, M, fout);
                        fprintf(fin, "DISPLAY()\n");
                        fprintf(fd, "2\n");
                    }
                    i ++;
                }
                break;
            case 1:
                {
                    if (STATIC) break;
                    j = rand() % M;
                    if (b[j].deleted) {
                        list *temp = new_list_node(b + j);
                        quad_insert(root, temp, 0);
                        free_list(temp);
                        b[j].deleted = 0;
                        fprintf(fin, "INSERT(%s)\n", b[j].name);
                        fprintf(fd, "6 %s\n", b[i].name);
                        fprintf(fout, "%s IS INSERTED\n", b[j].name);
                        if (DISPLAY && ALL_DISPLAY) {
                            display(root, b, M, fout);
                        }
                    }
                    i ++;
                }
                break;
            case 2: 
                {
                    if (STATIC) break;
                    if (rand() % 5 == 0) {
                        point *p = a + rand() % N;
                        list *temp = quad_search(root, p), *it = temp;
                        int count = 0;
                        while (it != NULL) {
                            count ++;
                            it = it->next;
                        }
                        free_list(temp);
                        root = quad_delete_point(root, p);
                        fprintf(fin, "DELETE_POINT(%d,%d)\n", 
                            dround(p->x), dround(p->y));
                        fprintf(fd, "72 %d %d\n", 
                            dround(p->x), dround(p->y));
                        fprintf(fout, "%d LINE(S) DELETED\n", count);
                        if (DISPLAY && ALL_DISPLAY) {
                            fprintf(fout, "$$$$ SP(%.2lf,%.2lf)\n", 
                                (double) WIDTH, (double) WIDTH);
                            int j;
                            for (j = 0; j < M; j ++) {
                                if (! b[j].deleted) 
                                    edge_display(b + j, fout);
                            }
                            fprintf(fout, "DD(%.2lf,%.2lf,%d)\n", 
                                p->x, p->y, DOT_RADIUS);
                            fprintf(fout, "LD(%d,%d)\n", DASH_BLACK, DASH_WHITE);
                            window_display(& root->A, & root->B, fout);
                            quad_display(root, fout);
                            fprintf(fout, "EP\n");
                        }
                    }
                    else {
                        j = rand() % M;
                        if (! b[j].deleted) {
                            root = quad_delete(root, b + j);
                            b[j].deleted = 1;
                            fprintf(fin, "DELETE(%s)\n", b[j].name);
                            fprintf(fd, "71 %s\n", b[j].name);
                            fprintf(fout, "%s IS DELETED\n", b[j].name);
                            if (DISPLAY && ALL_DISPLAY) {
                                display(root, b, M, fout);
                            }
                        }
                    }
                    i ++;
                }
                break;
            case 3: 
                {
                    edge e;
                    point A = gen_point(), B = gen_point();
                    e.a = & A; e.b = & B;
                    bst *ret = new_bst();
                    quad_search_edge(root, & e, & ret);
                    fprintf(fin, "CREATE_LINE(%d,%d,%d,%d,%d)\n", ++ lines, 
                        dround(A.x), dround(A.y), dround(B.x), dround(B.y));
                    fprintf(fd, "4 %d %d %d %d %d\n", lines, 
                        dround(A.x), dround(A.y), dround(B.x), dround(B.y));
                    fprintf(fout, "%d IS CREATED\n", lines);
                    fprintf(fin, "LINE_SEARCH(%d)\n", lines);
                    fprintf(fd, "5 %d\n", lines);
                    if (ret->s == 0) 
                        fprintf(fout, 
                            "%d DOES NOT INTERSECT ANY EXISTING LINE\n", lines);
                    else 
                        fprintf(fout, 
                            "%d INTERSECTS %d LINE(S)\n", lines, ret->s);
                    if (DISPLAY && ALL_DISPLAY) {
                        fprintf(fout, "$$$$ SP(%.2lf,%.2lf)\n", 
                            (double) WIDTH, (double) WIDTH);
                        bst_display(ret, fout);
                        fprintf(fout, "LD(%d,%d)\n", DASH_BLACK, DASH_WHITE);
                        edge_display(& e, fout);
                        window_display(& root->A, & root->B, fout);
                        fprintf(fout, "EP\n");
                    }
                    if (BF_CHECK) {
                        int i, count = 0;
                        for (i = 0; i < M; i ++) {
                            if (b[i].deleted) continue;
                            if (edges_intersect(& e, b + i) != SEPARATE) {
                                count ++;
                                if (bst_search(ret, b + i) == NULL) {
                                    print_edge(b + i);
                                }
                            }
                        }
                        if (ret->s != count) {
                            printf("\n");
                            printf("edge: %lf %lf %lf %lf\n", 
                                A.x, A.y, B.x, B.y);
                        }
                    }
                    free_bst(ret);
                    i ++;
                }
                break;
            case 4:
                {
                    edge *e = NULL;
                    point A = gen_point();
                    quad_nearest(root, & A, & e);
                    fprintf(fin, "NEIGHBOR(%d,%d)\n", dround(A.x), dround(A.y));
                    fprintf(fd, "8 %d %d\n", dround(A.x), dround(A.y));
                    if (e == NULL) 
                        fprintf(fout, "THE LINE DOES NOT EXIST\n");
                    else 
                        fprintf(fout, "THE NEAREST NEIGHBOR IS %s\n", e->name);
                    if (DISPLAY && ALL_DISPLAY) {
                        fprintf(fout, "$$$$ SP(%.2lf,%.2lf)\n", 
                            (double) WIDTH, (double) WIDTH);
                        if (e != NULL) edge_display(e, fout);
                        fprintf(fout, "DD(%.2lf,%.2lf,%d)\n", 
                            A.x, A.y, DOT_RADIUS);
                        fprintf(fout, "LD(%d,%d)\n", DASH_BLACK, DASH_WHITE);
                        window_display(& root->A, & root->B, fout);
                        fprintf(fout, "EP\n");
                    }
                    if (e == NULL) {
                        if (BF_CHECK) {
                            int i;
                            for (i = 0; i < M; i ++) {
                                if (! b[i].deleted) 
                                    printf("nn: %d\n", i);
                            }
                        }
                    }
                    else {
                        int index = e - b;
                        if (index < 0 || index > M) {
                            printf("%d\n", index);
                        }
                        if (BF_CHECK) {
                            int i;
                            double d2_ = dist2_edge_point(e, & A);
                            for (i = 0; i < M; i ++) {
                                if (b[i].deleted) continue;
                                double d2 = dist2_edge_point(b + i, & A);
                                if (d2 < d2_) {
                                    printf("nn: %lf %lf\n", d2, d2_);
                                }
                            }
                        }
                    }
                    i ++;
                }
                break;
            case 5: 
                {
                    point A = gen_point(), B = gen_point();
                    if (A.x > B.x) {
                        double temp = A.x;
                        A.x = B.x;
                        B.x = temp;
                    }
                    if (A.y > B.y) {
                        double temp = A.y;
                        A.y = B.y;
                        B.y = temp;
                    }
                    bst *ret = new_bst();
                    quad_search_window(root, & A, & B, & ret);
                    if (DISPLAY) {
                        fprintf(fin, "WINDOW_DISPLAY(%d,%d,%d,%d)\n", 
                            dround(A.x), dround(A.y), dround(B.x), dround(B.y));
                        fprintf(fd, "102 %d %d %d %d\n", 
                            dround(A.x), dround(A.y), dround(B.x), dround(B.y));
                        fprintf(fout, "%d LINE(S) IN THE WINDOW\n", ret->s);
                        fprintf(fout, "$$$$ SP(%.2lf,%.2lf)\n", 
                            (double) WIDTH, (double) WIDTH);
                        bst_display(ret, fout);
                        fprintf(fout, "LD(%d,%d)\n", DASH_BLACK, DASH_WHITE);
                        window_display(& root->A, & root->B, fout);
                        window_display(& A, & B, fout);
                        fprintf(fout, "EP\n");
                    }
                    else {
                        fprintf(fin, "WINDOW(%d,%d,%d,%d)\n", 
                            dround(A.x), dround(A.y), dround(B.x), dround(B.y));
                        fprintf(fd, "101 %d %d %d %d\n", 
                            dround(A.x), dround(A.y), dround(B.x), dround(B.y));
                        fprintf(fout, "%d LINE(S) IN THE WINDOW\n", ret->s);
                    }
                    if (BF_CHECK) {
                        int count = 0;
                        for (j = 0; j < M; j ++) {
                            if (b[j].deleted) continue;
                            if (window_contain_edge(& A, & B, b + j)) {
                                count ++;
                                if (bst_search(ret, b + j) == NULL) {
                                    print_edge(b + j);
                                }
                            }
                        }
                        if (ret->s != count) {
                            printf("\n");
                            printf("window: %lf %lf %lf %lf\n", 
                                A.x, A.y, B.x, B.y);
                        }
                    }
                    free_bst(ret);
                    i ++;
                }
                break;
            case 6:
                {
                    i ++;
                }
                break;
            case 7: 
                {
                    int K = 10;
                    point *c = gen_polygon(K);
                    bst *ret = new_bst();
                    quad_search_polygon(root, c, K, & ret);
                    if (DISPLAY) {
                        fprintf(fin, "POLYGONAL_WINDOW_DISPLAY(%d,%d)\n", 
                            dround(c[0].x), dround(c[0].y));
                        int j;
                        for (j = 1; j < K; j ++) {
                            fprintf(fin, "VERTEX_WINDOW(%d,%d)\n", 
                                dround(c[j].x), dround(c[j].y));
                        }
                        fprintf(fin, "END_WINDOW()\n");
                        fprintf(fout, 
                            "%d LINE(S) IN THE POLYGONAL WINDOW\n", ret->s);
                        fprintf(fout, "$$$$ SP(%.2lf,%.2lf)\n", 
                            (double) WIDTH, (double) WIDTH);
                        bst_display(ret, fout);
                        fprintf(fout, "LD(%d,%d)\n", DASH_BLACK, DASH_WHITE);
                        polygon_display(c, K, fout);
                        window_display(& root->A, & root->B, fout);
                        fprintf(fout, "EP\n");
                    }
                    else {
                        fprintf(fin, "POLYGONAL_WINDOW(%d,%d)\n", 
                            dround(c[0].x), dround(c[0].y));
                        int j;
                        for (j = 1; j < K; j ++) {
                            fprintf(fin, "VERTEX_WINDOW(%d,%d)\n", 
                                dround(c[j].x), dround(c[j].y));
                        }
                        fprintf(fin, "END_WINDOW()\n");
                        fprintf(fout, 
                            "%d LINE(S) IN THE POLYGONAL WINDOW\n", ret->s);
                    }
                    if (BF_CHECK) {
                        int j, count = 0;
                        for (j = 0; j < M; j ++) {
                            if (b[j].deleted) continue;
                            if (polygon_intersect_edge(c, K, b + j)) {
                                count ++;
                                if (bst_search(ret, b + j) == NULL) {
                                    print_edge(b + j);
                                }
                            }
                        }
                        if (ret->s != count) {
                            printf("\n");
                            printf("polygon: %d %d\n", ret->s, count);
                        }
                    }
                    free_bst(ret);
                    free(c);
                    i ++;
                }
                break;
            case 8: 
                {
                    int K = rand() % 20 + 1;
                    edge **e = (edge **) malloc(sizeof(edge *) * K);
                    int j;
                    for (j = 0; j < K; j ++) 
                        e[j] = NULL;
                    point A = gen_point();
                    quad_k_nearest_bfs(root, & A, e, K);
                    fprintf(fin, "KTH_NEIGHBOR(%d,%d,%d)\n", 
                        dround(A.x), dround(A.y), K);
                    fprintf(fd, "9 %d %d %d\n", dround(A.x), dround(A.y), K);
                    if (e[K - 1] == NULL) 
                        fprintf(fout, "THE LINE DOES NOT EXIST\n");
                    else 
                        fprintf(fout, "THE KTH NEAREST NEIGHBOR IS %s\n", 
                            e[K - 1]->name);
                    if (DISPLAY && ALL_DISPLAY) {
                        fprintf(fout, "$$$$ SP(%.2lf,%.2lf)\n", 
                            (double) WIDTH, (double) WIDTH);
                        if (e[K - 1] != NULL) edge_display(e[K - 1], fout);
                        fprintf(fout, "DD(%.2lf,%.2lf,%d)\n", 
                            A.x, A.y, DOT_RADIUS);
                        fprintf(fout, "LD(%d,%d)\n", DASH_BLACK, DASH_WHITE);
                        for (j = 0; j < K - 1; j ++) 
                            if (e[j] != NULL) edge_display(e[j], fout);
                        window_display(& root->A, & root->B, fout);
                        fprintf(fout, "EP\n");
                    }
                    if (BF_CHECK) {
                        edge **e_ = (edge **) malloc(sizeof(edge *) * K);
                        for (j = 0; j < K; j ++) 
                            e_[j] = NULL;
                        int i_;
                        for (i_ = 0; i_ < M; i_ ++) {
                            if (b[i_].deleted) continue;
                            double d2 = dist2_edge_point(b + i_, & A);
                            int j, k;
                            for (j = 0; j < K; j ++) {
                                if (e_[j] == NULL) break;
                                double d2_ = dist2_edge_point(e_[j], & A);
                                int s = sgn(d2_ - d2);
                                if (s > 0 || (s == 0 
                                && strcmp(e_[j]->name, b[i_].name) > 0)) 
                                    break;
                            }
                            if (j < K) {
                                for (k = K - 1; k > j; k --) {
                                    e_[k] = e_[k - 1];
                                }
                                e_[j] = b + i_;
                            }
                        }
                        for (i_ = 0; i_ < K; i_ ++) {
                            if ((e[i_] != NULL && e_[i_] == NULL)
                             || (e[i_] == NULL && e_[i_] != NULL)
                             || (strcmp(e[i_]->name, e_[i_]->name) != 0)) {
                                printf("knn: %d %s %s %lf %lf\n", i_, 
                                    e[i_] == NULL ? 0 : e[i_]->name,
                                    e_[i_] == NULL ? 0 : e_[i_]->name,
                                    e[i_] == NULL ? 0 : dist2_edge_point(e[i_], & A),
                                    e_[i_] == NULL ? 0 : dist2_edge_point(e_[i_], & A));

                             }
                        }
                        free(e_);
                    }
                    free(e);
                    i ++;
                }
                break;
        }
    }
    printf("first group done: %d %d\n", quad_count, list_count);
    for (i = 0; i < M; i ++) {
        if (STATIC) continue;
        if (b[i].deleted) {
            fprintf(fin, "INSERT(%s)\n", b[i].name);
            list *temp = new_list_node(b + i);
            quad_insert(root, temp, 0);
            free_list(temp);
            b[i].deleted = 0;
            fprintf(fd, "6 %s\n", b[i].name);
            fprintf(fout, "%s IS INSERTED\n", b[i].name);
        }
    }
    if (DISPLAY) {
        fprintf(fin, "DISPLAY()\n");
        fprintf(fd, "2\n");
        display(root, b, M, fout);
    }
    if (type[6] > 0) {
        int X = 0, Y = 0;
        for (i = 0; i < type[6]; i ++) {
            point *temp;
            int K;
            point c = gen_point();
            fprintf(fin, "FIND_POLYGON(%d,%d)\n", dround(c.x), dround(c.y));
            fprintf(fd, "11 %d %d\n", dround(c.x), dround(c.y));
            quad_point_location(root, & c, & temp, & K, fout);
            if (K == 0) {
                X ++;
            }
            else {
                Y ++;
                //assert(K == 3);
                free(temp);
            }
        }
        printf("second group done: %d %d\n", quad_count, list_count);
        printf("pi = %lf\n", (double) Y / (X + Y) * 4);
    }
    printf("op: ");
    for (i = 0; i < OP_TYPE; i ++) 
        printf("%d ", type[i]);
    printf("\n");
    free_bst(dict);
    free_quad(root);
    free(a);
    free(b);
    printf("clean: %d %d %d %d\n", quad_count, list_count, bst_count, heap_count);
    fclose(fin);
    fclose(fout);
}

void init() {
    init_bst();
    clock_t t = time(0);
    srand(t);
    printf("seed: %d\n", t);
}

int main() {
    init();
    test_file("mesh.txt", "input.txt", "decode.txt", "output.txt", 128);
    return EXIT_SUCCESS;
}
