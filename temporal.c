/*
Errata of the paper：
    1. The example of Huffman coding in the L&C section is a typo;
    2. The average coding length of L&C in experiments 
        did NOT count the first edge, 
        so the compression ratio may be slightly lower;
    3. Time costs of temporal comperssion algorithms in experiments 
        are w.r.t a smaller test set (10^6 ~ 10^7 tuples) 
        (it was confused with the set for spatial compression);
    4. The indexed query processing approach could be faster 
        if binary search used instead of building trees, 
        while search through the partial approach 
        could take advantage of binary search too.
    5. to be continued ... : P

Information about the polygon division:
    If tests are on real data, 
    then stationary situation is inevitable,
    which does not happen in generated data.
    In this case please implement polygon division 
    introduced in the paper (temporal compression section).

About the implementation of this algorithm:
    1. Splay trees or finger trees are not implemented 
        because a funnel in practice only contains 
        2-3 vertices in average.
        So it would be even more time-consuming 
        when these indices are used.
        Anyway, it is interesting to replace the 
        linked list used in the funnel structure 
        to see whether the conclusion above is true.
    2. Re-triangulation may be faster 
        if an O(n) algorithm is used.
        I tried the O(n) algorithm for monotone polygons 
        but it has not been proved right theoretically.
        There is an O(n) algorithm for a weak visible polygon 
        where all points inside the polygon 
        are visible to a chord in it.
        This algorithm is proved appropriate.
        Again, further exploration as well as 
        experiments on this could be interesting.
    3. The problem of floating-point number precision 
        can not be resolved in C language, 
        so hopefully this program could be 
        re-written in other languages like Java or Python.
        Due to the precision limitations, 
        errors may occur when tau or eta is close to 0.
        Furthermore, it may leads to the problem 
        that differences between the input and the output 
        exceed the error bounds a little, 
        which is mainly because of line intersection calculation.
        Notwithstanding, it is good for real-world applications.

This program should only be shared within the MDM group.
Do NOT make it public without the permission of Prof. Sun.

If you have any other problems, contact me via
yunhenghan19 at gmail dot com.
*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

#define MAX_vertices 5000000
#define MAX_pointer_buffers 10
#define EPS 1e-8
#define INF  1e8
#define MONOTONE_ONLY 1
#define SKIP_DP_N 100000
#define SHOW_DETAIL 0

typedef struct sp_record {
    struct vertex *parent;
    int depth, convex;
    double cross;
} sp_record;

typedef struct vertex {
    int id;
    double x, y;
    struct edge *in, *out, *head;
    int side;
    sp_record *sp[2];
} vertex;

typedef struct edge {
    vertex *from, *to, *helper;
    struct edge *next, *prev, *twin;
    struct facet *left_hand;
    int to_delete;
} edge;

typedef struct facet {
    edge *loop;
    int visited;
} facet;

typedef struct polytope {
    int N, M, L, series_len;
    vertex **vertices;
    facet *external;
} polytope;

typedef struct bst_node {
    edge *e;
    struct bst_node *left, *right;
    int h;
} bst_node;

typedef struct chain_node {
    vertex *v;
    struct chain_node *next;
} chain_node;

typedef struct funnel {
    // can be a splay tree or finger tree
    // but more efficient in practice where funnels are short
    vertex *apex;
    chain_node *left_chain, *right_chain;
} funnel;

typedef struct window {
    vertex *v0, *v1;
    edge *e0, *e1;
    polytope *p;
    struct window *parent;
    int depth, to_split;
} window;

typedef struct series {
    double **list;
    int N;
} series;

void ***pointer_buffers;
int *avail_pointer_buffer, max_buffers,
    bst_node_count, vertex_count[2], edge_count[2], facet_count[2],
    funnel_count[2], chain_node_count[2], window_count, 
    VERTEX_SEARCH_COUNT, FACET_SEARCH_COUNT, 
    START_TIME;
char string_buffer[65536];
bst_node *BST_NULL;
edge *SOURCE, *DESTINATION;
window *last_win;

void handle_exception(int assertion, char *message) {
    if (! assertion) 
        printf("*** %s ***\n", message);
    assert(assertion);
}

double rand_float(double d) {
    if (d == 0) 
        return rand() + rand() / RAND_MAX;
    else 
        return (rand() + rand() / RAND_MAX) * d / (RAND_MAX + 1);
}

int rand_int(int mod) {
    return (rand() * RAND_MAX + rand()) % mod;
}

int sgn(double x) {
    if (-EPS < x && x < EPS) return 0;
    if (x < 0) return -1;
    return 1;
}

double dabs(double x) {
    if (x < 0) return - x;
    return x;
}

double dist2(vertex *v1, vertex *v2) {
    return (v1->x - v2->x) * (v1->x - v2->x) 
        + (v1->y - v2->y) * (v1->y - v2->y);
}

double cross(vertex *v1, vertex *v2, vertex *u1, vertex *u2) {
    double x1 = v2->x - v1->x, y1 = v2->y - v1->y;
    double x2 = u2->x - u1->x, y2 = u2->y - u1->y;
    return x1 * y2 - x2 * y1;
}

double xat(double x0, double y0, double x1, double y1, double y) {
    int dy = sgn(y1 - y0);
    if (dy == 0) return x0;
    if (dabs(y - y0) > dabs(y1 - y)) {
        double r = (y - y0) / (y1 - y0);
        return x0 + (x1 - x0) * r;
    }
    else {
        double r = (y1 - y) / (y1 - y0);
        return x1 - (x1 - x0) * r;
    }
}

double xat_2(edge *e, double y) {
    return xat(e->from->x, e->from->y, e->to->x, e->to->y, y);
}

double yat(double x0, double y0, double x1, double y1, double x) {
    int dx = sgn(x1 - x0);
    if (dx == 0) return y0;
    if (dabs(x - x0) > dabs(x1 - x)) {
        double r = (x - x0) / (x1 - x0);
        return y0 + (y1 - y0) * r;
    }
    else {
        double r = (x1 - x) / (x1 - x0);
        return y1 - (y1 - y0) * r;
    }
}

double area_of(facet *f) {
    double S = 0;
    edge *e = f->loop;
    do {
        double x1 = e->from->x, y1 = e->from->y, 
            x2 = e->to->x, y2 = e->to->y;
        S += x1 * y2 - x2 * y1;
        e = e->next;
    } while (e != f->loop);
    return S;
}

int compare_point_cartesian(vertex *v1, vertex *v2) {
    int dy = sgn(v1->y - v2->y);
    if (dy != 0) return dy;
    int dx = sgn(v1->x - v2->x);
    return dx;
}

int compare_point_polar(vertex *center, vertex *v1, vertex *v2) {
    int c12 = sgn(cross(center, v1, center, v2));
    return c12;
}

void sort_by_cartesian(vertex **queue, int l, int r) {
    int i = l, j = r;
    vertex *mid = queue[(l + r) / 2];
    while (i <= j) {
        while (compare_point_cartesian(queue[i], mid) == 1) i ++;
        while (compare_point_cartesian(mid, queue[j]) == 1) j --;
        if (i <= j) {
            vertex *temp = queue[i];
            queue[i] = queue[j];
            queue[j] = temp;
            i ++;
            j --;
        }
    }
    if (i < r) sort_by_cartesian(queue, i, r);
    if (l < j) sort_by_cartesian(queue, l, j);
}

void sort_by_polar(vertex **queue, vertex *center, int l, int r) {
    int i = l, j = r;
    vertex *mid = queue[(l + r) / 2];
    while (i <= j) {
        while (compare_point_polar(center, queue[i], mid) == 1) i ++;
        while (compare_point_polar(center, mid, queue[j]) == 1) j --;
        if (i <= j) {
            vertex *temp = queue[i];
            queue[i] = queue[j];
            queue[j] = temp;
            i ++;
            j --;
        }
    }
    if (i < r) sort_by_polar(queue, center, i, r);
    if (l < j) sort_by_polar(queue, center, l, j);
}

void sort_by_address(facet **queue, int l, int r) {
    int i = l, j = r;
    facet *mid = queue[(l + r) / 2];
    while (i <= j) {
        while (queue[i] < mid) i ++;
        while (queue[j] > mid) j --;
        if (i <= j) {
            facet *temp = queue[i];
            queue[i] = queue[j];
            queue[j] = temp;
            i ++;
            j --;
        }
    }
    if (i < r) sort_by_address(queue, i, r);
    if (l < j) sort_by_address(queue, l, j);
}

void sort_by_address_2(facet **queue, int l, int r) {
    int i, j;
    for (i = l; i <= r; i ++) {
        for (j = i + 1; j <= r; j ++) {
            if (queue[i] > queue[j]) {
                facet *temp = queue[i];
                queue[i] = queue[j];
                queue[j] = temp;
            }
        }
    }
}

int check_segments_touch(vertex *v0, vertex *v1, vertex *v2, vertex *v3) {
    double c203 = cross(v2, v0, v2, v3);
    double c231 = cross(v2, v3, v2, v1);
    double c021 = cross(v0, v2, v0, v1);
    double c013 = cross(v0, v1, v0, v3);
    int d203 = sgn(c203), d231 = sgn(c231), 
        d021 = sgn(c021), d013 = sgn(c013);
    if (d203 == 0 && d231 == 0) {
        assert(d021 == 0 && d013 == 0);
        double d[5];
        if  (dabs(v0->x - v1->x) > dabs(v0->y - v1->y)) {
            d[0] = dabs(v0->x - v2->x);
            d[1] = dabs(v0->x - v3->x);
            d[2] = dabs(v1->x - v2->x);
            d[3] = dabs(v1->x - v3->x);
            d[4] = dabs(v0->x - v1->x) + dabs(v2->x - v3->x);
        }
        else {
            d[0] = dabs(v0->y - v2->y);
            d[1] = dabs(v0->y - v3->y);
            d[2] = dabs(v1->y - v2->y);
            d[3] = dabs(v1->y - v3->y);
            d[4] = dabs(v0->y - v1->y) + dabs(v2->x - v3->y);
        }
        int i, j = -1;
        for (i = 0; i < 4; i ++) 
            if (j == -1 || d[i] > d[j]) 
                j = i;
        if (sgn(d[j] - d[5]) <= 0) 
            return 1;
        else 
            return 0; 
    }
    return (d203 * d231 >= 0 && d021 * d013 >= 0);
}

int check_separate(vertex *v0, vertex *v1, vertex *v2, vertex *v3) {
    double c203 = cross(v2, v0, v2, v3);
    double c231 = cross(v2, v3, v2, v1);
    return (c203 < 0 && c231 <0) || (c203 > 0 && c231 > 0);
}

int check_segments_intersect(
    vertex *v0, vertex *v1, vertex *v2, vertex *v3) 
{
    double c203 = cross(v2, v0, v2, v3);
    double c231 = cross(v2, v3, v2, v1);
    double c021 = cross(v0, v2, v0, v1);
    double c013 = cross(v0, v1, v0, v3);
    return ((c203 < 0 && c231 < 0) || (c203 > 0 && c231 > 0)) &&
        ((c021 < 0 && c013 < 0) || (c021 > 0 && c013 > 0));
}

int check_on_segment(vertex *v0 ,vertex *v1, vertex *v2) {
    double c012 = cross(v0, v1, v0, v2);
    int d012 = sgn(c012);
    if (d012 == 0) {
        double d[3];
        if  (dabs(v1->x - v2->x) > dabs(v1->y - v2->y)) {
            d[0] = dabs(v1->x - v0->x);
            d[1] = dabs(v0->x - v2->x);
            d[2] = dabs(v1->x - v2->x);
        }
        else {
            d[0] = dabs(v1->y - v0->y);
            d[1] = dabs(v0->y - v2->y);
            d[2] = dabs(v1->y - v2->y);
        }
        if (sgn((d[0] + d[1] - d[2])) == 0) 
            return 1;
    }
    return 0;
}

vertex *new_vertex(double x, double y, int id);

vertex *segment_line_intersect(
    vertex *v0, vertex *v1, vertex *v2, vertex *v3) 
{
    double c203 = cross(v2, v0, v2, v3);
    double c231 = cross(v2, v3, v2, v1);
    int d203 = sgn(c203), d231 = sgn(c231);
    assert(d203 != 1 || d231 != 1);
    if (d203 == 1 || d231 == 1) return NULL;
    if (d203 == 0) {
        if (d231 != 0) 
            return v0;
        else {
            if (dist2(v3, v0) < dist2(v3, v1))
                return v0;
            else 
                return v1;
        }
    }
    if (d231 == 0) return v1;
    double r = c203 / (c203 + c231);
    vertex *v = new_vertex(v0->x + r * (v1->x - v0->x), 
        v0->y + r * (v1->y - v0->y), 0);
    return v;
}

vertex *lines_intersect(
    vertex *v0, vertex *v1, vertex *v2, vertex *v3) 
{
    double cr = (v0->x - v1->x) * (v2->y - v3->y) 
        - (v0->y - v1->y) * (v2->x - v3->x);
    if (sgn(cr) == 0) return NULL;
    assert(cr == cross(v1, v0, v3, v2));
    double cr01 = v0->x * v1->y - v0->y * v1->x;
    double cr23 = v2->x * v3->y - v2->y * v3->x;
    double x = (cr01 * (v2->x - v3->x) - (v0->x - v1->x) * cr23) / cr;
    double y = (cr01 * (v2->y - v3->y) - (v0->y - v1->y) * cr23) / cr;
    vertex *v = new_vertex(x, y, 0);
    return v;
}

void new_pointer_buffers() {
    max_buffers = 0;
    avail_pointer_buffer = (int *) malloc(
        sizeof(int) * MAX_pointer_buffers);
    pointer_buffers = (void ***) malloc(
        sizeof(void **) * MAX_pointer_buffers);
    int i;
    for (i = 0; i < MAX_pointer_buffers; i ++) {
        pointer_buffers[i] = (void **) malloc(
            sizeof(void *) * MAX_vertices);
        avail_pointer_buffer[i] = 1;
    }
}

void free_pointer_buffers() {
    int i;
    for (i = 0; i < MAX_pointer_buffers; i ++) {
        assert(avail_pointer_buffer[i]);
        free(pointer_buffers[i]);
    }
    free(pointer_buffers);
    if (SHOW_DETAIL) {
        printf("   - %d pointer buffers used\n", max_buffers);
    }
}

void** get_buffer() {
    int i;
    int temp = 0;
    for (i = 0; i < MAX_pointer_buffers; i ++) 
        if (! avail_pointer_buffer[i]) 
            temp ++;
    if (temp > max_buffers) max_buffers = temp;
    for (i = 0; i < MAX_pointer_buffers; i ++) 
        if (avail_pointer_buffer[i]) {
            avail_pointer_buffer[i] = 0;
            return pointer_buffers[i];
        }
    assert(0);
}

void return_buffer(void ** buffer) {
    int i;
    for (i = 0; i < MAX_pointer_buffers; i ++)
        if (buffer == pointer_buffers[i])
            avail_pointer_buffer[i] = 1;
    assert(i == MAX_pointer_buffers);
}

vertex *new_vertex(double x, double y, int id) {
    vertex *v = (vertex *) malloc(sizeof(vertex));
    vertex_count[0] ++;
    vertex_count[1] ++;
    v->x = x;
    v->y = y;
    v->id = id;
    v->sp[0] = (sp_record *) malloc(sizeof(sp_record));
    v->sp[1] = (sp_record *) malloc(sizeof(sp_record));
    v->sp[0]->parent = NULL;
    v->sp[1]->parent = NULL;
    return v;
}

void free_vertex(vertex *v) {
    free(v->sp[0]);
    free(v->sp[1]);
    free(v);
    vertex_count[0] --;
}

int sprint_vertex(char *string_buffer, vertex *v) {
    return sprintf(string_buffer, 
        "<%d: %lf %lf> ", v->id, v->x, v->y);
}

void print_vertex(vertex *v) {
    sprint_vertex(string_buffer, v);
    printf("%s", string_buffer);
}

int id_of(vertex *v) {
    if (v == NULL) 
        return 0;
    else 
        return v->id;
}

edge *new_edge() {
    edge *e = (edge *) malloc(sizeof(edge));
    edge_count[0] ++;
    edge_count[1] ++;
    e->to_delete = 0;
    return e;
}

void *free_edge(edge *e) {
    free(e);
    edge_count[0] --;
}

int sprint_edge(char *string_buffer, edge *e) {
    int len = 0;
    len += sprintf(string_buffer, "( ");
    len += sprint_vertex(string_buffer + len, e->from);
    len += sprintf(string_buffer + len, ", ");
    len += sprint_vertex(string_buffer + len, e->to);
    len += sprintf(string_buffer + len, ") ");
    return len;
}

void print_edge(edge *e) {
    sprint_edge(string_buffer, e);
    printf("%s", string_buffer);
}

facet *new_facet() {
    facet *f = (facet *) malloc(sizeof(facet));
    f->visited = 0;
    facet_count[0] ++;
    facet_count[1] ++;
    return f;
}

void free_facet(facet *f) {
    free(f);
    facet_count[0] --;
}

int sprint_facet(char *string_buffer, facet *f) {
    edge *e = f->loop;
    int len = 0;
    len += sprintf(string_buffer, "[ ");
    do {
        len += sprintf(string_buffer + len, "%d ", e->from->id);
        e = e->next;
    } while (e != f->loop);
    len += sprintf(string_buffer + len, "]\n");
    return len;
}

void print_facet(facet *f) {
    sprint_facet(string_buffer, f);
    printf("%s", string_buffer);
}

bst_node *new_bst_node(edge *e) {
    bst_node *b = (bst_node *) malloc(sizeof(bst_node));
    bst_node_count ++;
    b->e = e;
    b->left = b->right = BST_NULL;
    b->h = 0;
    return b;
}

void free_bst_node(bst_node *b) {
    free(b);
    bst_node_count --;
}

void new_bst() {
    BST_NULL = new_bst_node(NULL);
    BST_NULL->left = BST_NULL->right = BST_NULL;
    BST_NULL->h = -1;
}

void free_bst() {
    free_bst_node(BST_NULL);
    assert(bst_node_count == 0);
}

void update(bst_node *root) {
    if (root->left->h > root->right->h)
        root->h = root->left->h + 1;
    else
        root->h = root->right->h + 1;
}

bst_node *rotate_right(bst_node *root) {
    bst_node *temp = root->left;
    root->left = temp->right;
    temp->right = root;
    update(root); update(temp);
    return temp;
}

bst_node *rotate_left(bst_node *root) {
    bst_node *temp = root->right;
    root->right = temp->left;
    temp->left = root;
    update(root); update(temp);
    return temp;
}

bst_node *re_balance(bst_node *root) {
    if (root->left->h > root->right->h + 1) {
        if (root->left->left->h >= root->left->right->h)
            root = rotate_right(root);
        else {
            root->left = rotate_left(root->left);
            root = rotate_right(root);
        }
    }
    if (root->right->h > root->left->h + 1) {
        if (root->right->right->h >= root->right->left->h)
            root = rotate_left(root);
        else {
            root->right = rotate_right(root->right);
            root = rotate_left(root);
        }
    }
    return root;
}

bst_node *bst_insert(bst_node *root, edge *e, double y) {
    if (root == BST_NULL) {
        bst_node *temp = new_bst_node(e);
        return temp;
    }
    double xe = xat_2(e, y), xroot = xat_2(root->e, y);
    if (xe < xroot)
        root->left = bst_insert(root->left, e, y);
    else
        root->right = bst_insert(root->right, e, y);
    update(root);
    root = re_balance(root);
    return root;
}

bst_node *bst_delmax(bst_node *root, bst_node **temp) {
    if (root->right == BST_NULL) {
        *temp = root;
        return root->left;
    }
    root->right = bst_delmax(root->right, temp);
    update(root);
    root = re_balance(root);
    return root;
}

bst_node *bst_delete(bst_node *root, edge *e, double y) {
    if (root->e == e) {
        bst_node *temp = NULL;
        if (root->left == BST_NULL) {
            temp = root->right;
            free_bst_node(root);
            return temp;
        }
        if (root->right == BST_NULL) {
            temp = root->left;
            free_bst_node(root);
            return temp;
        }
        root->left = bst_delmax(root->left, &temp);
        root->e = temp->e;
        free_bst_node(temp);
        update(root);
        root = re_balance(root);
        return root;
    }
    double xe = xat_2(e, y), xroot = xat_2(root->e, y);
    if (xe < xroot)
        root->left = bst_delete(root->left, e, y);
    else
        root->right = bst_delete(root->right, e, y);
    update(root);
    root = re_balance(root);
    return root;
}

bst_node *search_prec(bst_node *root, double x, double y) {
    if (root == BST_NULL) return BST_NULL;
    double xroot = xat_2(root->e, y);
    if (x <= xroot)
        return search_prec(root->left, x, y);
    bst_node *temp = search_prec(root->right, x, y);
    if (temp == BST_NULL)
        return root;
    else
        return temp;
}

int sprint_bst(char *string_buffer, bst_node *root, double y) {
    if (root == BST_NULL) {
        return sprintf(string_buffer, "BST_NULL ");
    }
    int len = 0;
    if (root->left != BST_NULL) 
        len += sprint_bst(string_buffer, root->left, y);
    len += sprintf(string_buffer + len, "<");
    len += sprint_edge(string_buffer + len, root->e); 
    len += sprintf(string_buffer + len, "%.2lf> ", xat_2(root->e, y));
    if (root->right != BST_NULL) 
        len += sprint_bst(string_buffer + len, root->right, y);
    return len;
}

void print_bst(bst_node *root, double y) {
    sprint_bst(string_buffer, root, y);
    printf("%s", string_buffer);
}

void structuralize(polytope *p) {
    assert(p->external == NULL);
    assert(p->N >= 3);
    facet *internal = new_facet();
    facet *external = new_facet();

    int i = 2, j = 1;
    while (i < p->N) {
        while (i < p->N && 
        sgn(cross(p->vertices[j - 1], p->vertices[j], 
            p->vertices[j], p->vertices[i])) == 0)
        {
            free_vertex(p->vertices[j]);
            p->vertices[j] = p->vertices[i];
            i ++;
        }
        if (i < p->N) {
            j ++;
            p->vertices[j] = p->vertices[i];
            i ++;
        }
    }
    j ++;
    p->L = p->N = j;
    for (i = p->N; i < p->M; i ++) 
        p->vertices[i] = NULL;
    
    for (i = 0; i < p->N; i ++) {
        edge *e0 = new_edge();
        edge *e1 = new_edge();
        edge *last_e0, *last_e1, *first_e0, *first_e1;
        p->vertices[i]->head = e0;
        p->vertices[i]->out = p->vertices[i]->in = NULL;
        e0->twin = e1;
        e1->twin = e0;
        e0->left_hand = internal;
        e1->left_hand = external;
        e0->helper = e1->helper = NULL;
        if (i == p->N - 1) {
            e0->from = p->vertices[i];
            e0->to = p->vertices[0];
            e1->from = p->vertices[0];
            e1->to = p->vertices[i];
            e0->next = first_e0;
            first_e0->prev = e0;
            e1->prev = first_e1;
            first_e1->next = e1;
        }
        else {
            e0->from = p->vertices[i];
            e0->to = p->vertices[i + 1];
            e1->from = p->vertices[i + 1];
            e1->to = p->vertices[i];
        }
        if (i == 0) {
            first_e0 = e0;
            first_e1 = e1;
            internal->loop = e0;
            external->loop = e1;
        }
        else {
            last_e0->next = e0;
            e0->prev = last_e0;
            e1->next = last_e1;
            last_e1->prev = e1;
        }
        last_e0 = e0;
        last_e1 = e1;
    }
    p->external = external;
}

polytope *new_polygon_from(char *file_name) {
    vertex_count[0] = edge_count[0] = facet_count[0] = 0;
    vertex_count[1] = edge_count[1] = facet_count[1] = 0;
    FILE *fin = fopen(file_name, "r");
    int N;
    fscanf(fin, "%d", &N);
    polytope *p = (polytope *) malloc(sizeof(polytope));
    p->N = N;
    p->M = MAX_vertices;
    p->L = p->N;
    assert(p->M >= p->N);
    p->vertices = (vertex **) malloc(sizeof(vertex *) * p->M);
    int i;
    for (i = 0; i < p->N; i ++) {
        double x, y;
        fscanf(fin, "%lf%lf", &x, &y);
        p->vertices[i] = new_vertex(x, y, i + 1);
    }
    fclose(fin);
    for (i = p->N; i < p->M; i ++) 
        p->vertices[i] = NULL;
    p->external = NULL;
    structuralize(p);
    return p;
}

polytope *gen_polygon(int N) {
    vertex_count[0] = edge_count[0] = facet_count[0] = 0;
    vertex_count[1] = edge_count[1] = facet_count[1] = 0;
    polytope *p = (polytope *) malloc(sizeof(polytope));
    p->N = N;
    p->M = MAX_vertices;
    p->L = p->N;
    assert(p->M >= p->N);
    p->vertices = (vertex **) malloc(sizeof(vertex *) * p->M);
    int i;
    for (i = 0; i < N; i ++) {
        p->vertices[i] = new_vertex(
            rand_float(0), rand_float(0), i + 1);
        if (i != 0 && 
            compare_point_cartesian(
            p->vertices[0], p->vertices[i]) == -1) 
        {
            vertex *temp = p->vertices[i];
            p->vertices[i] = p->vertices[0];
            p->vertices[0] = temp;
        }
    }
    sort_by_polar(p->vertices, p->vertices[0], 1, N - 1);
    for (i = p->N; i < p->M; i ++) 
        p->vertices[i] = NULL;
    p->external = NULL;
    structuralize(p);
    return p;
}

series *new_series(int N) {
    series *s = (series *) malloc(sizeof(series));
    s->N = N;
    s->list = (double **) malloc(sizeof(double *) * N);
    int i;
    for (i = 0; i < N; i ++) 
        s->list[i] = (double *) malloc(sizeof(double) * 2);
    return s;
}

void free_series(series *s) {
    int i;
    for (i = 0; i < s->N; i ++) 
        free(s->list[i]);
    free(s->list);
    free(s);
}

series *new_series_from(char *file_name) {
    // if the tube is to be generated from file \
    polygon division should be applied \
    please refer to the paper
    FILE *fin = fopen(file_name, "r");
    int N;
    scanf("%d", & N);
    series *s = new_series(N);
    int i;
    for (i = 0; i < N; i ++) 
        scanf("%lf%lf", s->list[i], s->list[i] + 1);
    fclose(fin);
    printf("   - series length = %d\n", s->N);
    printf(" - series loaded\n");
    return s;
}

series *gen_series(int N, double dx, double dy) {
    series *s = new_series(N);
    int i;
    double x = 0, y = 0;
    for (i = 0; i < N; i ++) {
        // a bias of 0.01 is involved to avoid non-simple polygon
        // please use polygon division to get rid of this
        x += rand_float(dx) + 0.005;
        y += rand_float(dy) + 0.005;
        s->list[i][0] = x;
        s->list[i][1] = y;
    }
    printf("   - sampling rate <= %lf, velocity <= %lf\n", 
        dy, dx / dy);
    printf("   - series length = %d\n", s->N);
    printf(" - series generated - %dms\n", clock() - START_TIME);
    START_TIME = clock();
    return s;
}

void print_series(series *s) {
    int i;
    for (i = 0; i < s->N; i ++) 
        printf("%lf,%lf ", s->list[i][0], s->list[i][1]);
    printf("\n");
}

void check_result(series *s, series *t, double tau, double eta) {
    double eta_0 = 0;
    int i, j;
    for (i = 0, j = 0; i < s->N && j < t->N; ) {
        if (s->list[i][0] < t->list[j][0]) {
            if (j != 0) {
                double y = yat(t->list[j - 1][0], t->list[j - 1][1], 
                    t->list[j][0], t->list[j][1], s->list[i][0]);
                double delta = dabs(y - s->list[i][1]);
                if (delta > eta_0) {
                    eta_0 = delta;
                    //if (delta > eta) printf("%d %d\n", i, j);
                }
            }
            i ++;
        }
        else {
            if (i != 0) {
                double y = yat(s->list[i - 1][0], s->list[i - 1][1], 
                    s->list[i][0], s->list[i][1], t->list[j][0]);
                double delta = dabs(y - t->list[j][1]);
                if (delta > eta_0) {
                    eta_0 = delta;
                    //if (delta > eta) printf("%d %d\n", i, j);
                }
            }
            j ++;
        }
    }
    double tau_0 = 0;
    for (i = 0, j = 0; i < s->N && j < t->N; ) {
        if (s->list[i][1] < t->list[j][1]) {
            if (j != 0) {
                double x = xat(t->list[j - 1][0], t->list[j - 1][1], 
                    t->list[j][0], t->list[j][1], s->list[i][1]);
                double delta = dabs(x - s->list[i][0]);
                if (delta > tau_0) {
                    tau_0 = delta;
                    //if (delta > tau) printf("%d %d\n", i, j);
                }
            }
            i ++;
        }
        else {
            if (i != 0) {
                double x = xat(s->list[i - 1][0], s->list[i - 1][1], 
                    s->list[i][0], s->list[i][1], t->list[j][1]);
                double delta = dabs(x - t->list[j][0]);
                if (delta > tau_0) {
                    tau_0 = delta;
                    //if (delta > tau) printf("%d %d\n", i, j);
                }
            }
            j ++;
        }
    }
    printf("     - error: tau = %lf eta = %lf\n", tau_0, eta_0);
}

series *greedy_link_path(series *s, double tau, double eta) {
    vertex **result = (vertex **) get_buffer();
    int i = 1, j = 0, k = 0;
    vertex low, high, origin;
    origin.x = origin.y = 0;
    while (i < s->N) {
        if (k > 0) {
            vertex left, right, up, down, center;
            center.x = s->list[i][1] - s->list[j][1];
            center.y = s->list[i][0] - s->list[j][0];
            if (sgn(cross(& origin, & high, & origin, & center)) <= 0 && 
                sgn(cross(& origin, & low, & origin, & center)) >= 0) 
            {
                left.x = center.x - eta; left.y = center.y;
                right.x = center.x + eta; right.y = center.y;
                up.x = center.x; up.y = center.y + tau;
                down.x = center.x; down.y = center.y - tau;
                if (cross(& origin, & high, & origin, & up) < 0) high = up;
                if (cross(& origin, & high, & origin, & left) < 0) high = left;
                if (cross(& origin, & low, & origin, & down) > 0) low = down;
                if (cross(& origin, & low, & origin, & right) > 0) low = right;
                i ++;
                continue;
            }
        }
        j = i - 1;
        result[k ++] = new_vertex(s->list[j][0], s->list[j][1], 0);
        low.x = 0; low.y = - 1;
        high.x = 0; high.y = 1;
    }
    result[k ++] = new_vertex(s->list[s->N - 1][0], s->list[s->N - 1][1], 0);
    series *t = new_series(k);
    for (i = 0; i < k; i ++) {
        t->list[i][0] = result[i]->x;
        t->list[i][1] = result[i]->y;
        free_vertex(result[i]);
    }
    return_buffer((void **) result);
    printf("     - links = %d\n", k);
    printf("     - compression ratio = %lf\n", (double) s->N / k);
    check_result(s, t, tau, eta);
    printf("   - baseline greedy computed - %dms\n", clock() - START_TIME);
    START_TIME = clock();
    return t;
}

void DP_link_path_init_visible(
    series *s, double tau, double eta, int **visible) 
{
    int i, j;
    for (i = 0; i < s->N; i ++) {
        for (j = 0; j < s->N; j ++) {
            visible[i][j] = 0;
        }
    }
    vertex origin;
    origin.x = origin.y = 0;
    for (i = 0; i < s->N; i ++) {
        vertex low, high;
        low.x = 0; low.y = - 1;
        high.x = 0; high.y = 1;
        for (j = i - 1; j >= 0; j --) {
            vertex left, right, up, down, center;
            center.x = s->list[j][1] - s->list[i][1];
            center.y = s->list[j][0] - s->list[i][0];
            left.x = center.x - eta; left.y = center.y;
            right.x = center.x + eta; right.y = center.y;
            up.x = center.x; up.y = center.y + tau;
            down.x = center.x; down.y = center.y - tau;
            if (cross(& origin, & high, & origin, & up) > 0) high = up;
            if (cross(& origin, & high, & origin, & left) > 0) high = left;
            if (cross(& origin, & low, & origin, & down) < 0) low = down;
            if (cross(& origin, & low, & origin, & right) < 0) low = right;
            if (sgn(cross(& origin, & high, & origin, & center)) >= 0 && 
                sgn(cross(& origin, & low, & origin, & center)) <= 0)
                visible[i][j] = 1;
        }
    }
}

series *DP_link_path(series *s, double tau, double eta) {
    if (s->N > SKIP_DP_N) {
        printf("   - baseline DP skipped\n");
        return ;
    }
    vertex **result = (vertex **) get_buffer();
    int *opt = (int *) malloc(sizeof(int) * s->N);
    int *prec = (int *) malloc(sizeof(int) * s->N);
    int **visible = (int **) malloc(sizeof(int *) * s->N);
    int i, j;
    for (i = 0; i < s->N; i ++) 
        visible[i] = (int *) malloc(sizeof(int) * s->N);
    DP_link_path_init_visible(s, tau, eta, visible);
    for (i = 0; i < s->N; i ++) {
        if (i == 0) {
            opt[i] = 1; prec[i] = -1;
            continue;
        }
        else {
            opt[i] = -1;
            for (j = 0; j < i; j ++) {
                if (visible[i][j]) {
                    int temp = opt[j] + 1;
                    if (opt[i] == -1 || temp < opt[i]) {
                        opt[i] = temp;
                        prec[i] = j;
                    }
                }
            }
        }
    }
    i = s->N - 1;
    j = opt[s->N - 1];
    while (i != -1) {
        result[-- j] = new_vertex(s->list[i][0], s->list[i][1], 0);
        i = prec[i];
    }
    assert(j == 0);
    series *t = new_series(opt[s->N - 1]);
    for (i = 0; i < opt[s->N - 1]; i ++) {
        t->list[i][0] = result[i]->x;
        t->list[i][1] = result[i]->y;
        free_vertex(result[i]);
    }
    return_buffer((void **) result);
    printf("     - links = %d\n", opt[s->N - 1]);
    printf("     - compression ratio = %lf\n", 
        (double) s->N / opt[s->N - 1]);
    check_result(s, t, tau, eta);
    for (i = 0; i < s->N; i ++) 
        free(visible[i]);
    free(visible);
    free(opt);
    free(prec);
    printf("   - baseline DP computed - %dms\n", clock() - START_TIME);
    START_TIME = clock();
    return t;
}

void segments_intersect(double x0, double y0, double y1, 
    double x1, double y2, double y3, double *x, double *y) {
    if (sgn(y2 - y3) == 0) {
        *x = x0;
        *y = y0;
    }
    else {
        double k = (y1 - y0) / (y2 - y3);
        *x = x1 - (x1 - x0) / (k + 1);
        *y = y2 - (y2 - y0) / (k + 1);
    }
}

polytope *gen_tube(series* s, double eta, double tau) {
    // small eta and tau may result in non-simple polygon 
    // this problem can be solved if high-precision \
    floating-point numbers used (e.g., in Java or Python)
    double **buffer = (double **) malloc(sizeof(double *) * s->N * 4);
    int i, j, len;
    for (i = 0; i < s->N * 4; i ++) 
        buffer[i] = (double *) malloc(sizeof(double) * 5);
    
    int lower, right;
    for (lower = right = 0, i = 0; lower < s->N && right < s->N; ) {
        switch (sgn(s->list[lower][0] - s->list[right][0] - eta)) {
            case -1: 
                buffer[i][0] = s->list[lower][0];
                buffer[i][1] = s->list[lower][1] - tau;
                if (right == 0) 
                    buffer[i][2] = s->list[0][1];
                else 
                    buffer[i][2] = yat(
                        s->list[right - 1][0] + eta, s->list[right - 1][1], 
                        s->list[right][0] + eta, s->list[right][1], 
                        s->list[lower][0]);
                i ++;
                lower ++;
                break;
            case 0: 
                buffer[i][0] = s->list[lower][0];
                buffer[i][1] = s->list[lower][1] - tau;
                buffer[i][2] = s->list[right][1];
                i ++;
                lower ++;
                right ++;
                break;
            case 1: 
                buffer[i][0] = s->list[right][0] + eta;
                buffer[i][1] = yat(
                    s->list[lower - 1][0], s->list[lower - 1][1] - tau, 
                    s->list[lower][0], s->list[lower][1] - tau, 
                    s->list[right][0] + eta);
                buffer[i][2] = s->list[right][1];
                i ++;
                right ++;
                break;
            default: 
                break;
        }
    } 
    assert(lower == s->N);

    for (len = i, i = 0, j = 0; i < len; i ++) {
        if (i == 0) {
            buffer[j][3] = buffer[i][0];
            if (buffer[i][1] > buffer[i][2]) 
                buffer[j][4] = buffer[i][1];
            else 
                buffer[j][4] = buffer[i][2];
            j ++;
        }
        else {
            if (buffer[i - 1][1] > buffer[i - 1][2]) {
                if (buffer[i][1] >= buffer[i][2]) {
                    buffer[j][3] = buffer[i][0];
                    buffer[j][4] = buffer[i][1];
                    j ++;
                }
                else {
                    segments_intersect(
                        buffer[i - 1][0], buffer[i - 1][1], buffer[i - 1][2],
                        buffer[i][0], buffer[i][1], buffer[i][2], 
                        buffer[j] + 3, buffer[j] + 4);
                    j ++;
                    buffer[j][3] = buffer[i][0];
                    buffer[j][4] = buffer[i][2];
                    j ++;
                }
            }
            else {
                if (buffer[i][1] <= buffer[i][2]) {
                    buffer[j][3] = buffer[i][0];
                    buffer[j][4] = buffer[i][2];
                    j ++;
                }
                else {
                    segments_intersect(
                        buffer[i - 1][0], buffer[i - 1][1], buffer[i - 1][2],
                        buffer[i][0], buffer[i][1], buffer[i][2], 
                        buffer[j] + 3, buffer[j] + 4);
                    j ++;
                    buffer[j][3] = buffer[i][0];
                    buffer[j][4] = buffer[i][1];
                    j ++;
                }
            }
        }
    }

    polytope *p = (polytope *) malloc(sizeof(polytope));
    p->M = s->N * 8;
    p->vertices = (vertex **) malloc(sizeof(vertex *) * p->M);
    p->N = 0;
    for (len = j, i = 0; i < len; i ++) {
        p->vertices[p->N] = new_vertex(buffer[i][3], buffer[i][4], p->N + 1);
        p->N ++;
    }

    int upper, left;
    for (upper = left = 0, i = 0; upper < s->N && left < s->N; ) {
        switch (sgn(s->list[upper][0] - s->list[left][0] + eta)) {
            case -1: 
                buffer[i][0] = s->list[upper][0];
                buffer[i][1] = s->list[upper][1] + tau;
                buffer[i][2] = yat(
                    s->list[left - 1][0] - eta, s->list[left - 1][1], 
                    s->list[left][0] - eta, s->list[left][1], 
                    s->list[upper][0]);
                i ++;
                upper ++;
                break;
            case 0: 
                buffer[i][0] = s->list[upper][0];
                buffer[i][1] = s->list[upper][1] + tau;
                buffer[i][2] = s->list[left][1];
                i ++;
                upper ++;
                left ++;
                break;
            case 1: 
                if (upper != 0) {
                    buffer[i][0] = s->list[left][0] - eta;
                    buffer[i][1] = yat(
                        s->list[upper - 1][0], s->list[upper - 1][1] + tau, 
                        s->list[upper][0], s->list[upper][1] + tau, 
                        s->list[left][0] - eta);
                    buffer[i][2] = s->list[left][1];
                    i ++;
                }
                left ++;
                break;
            default: 
                break;
        }
    }
    for ( ; upper < s->N; upper ++, i ++) {
        buffer[i][0] = s->list[upper][0];
        buffer[i][1] = s->list[upper][1] + tau;
        buffer[i][2] = s->list[s->N - 1][1];
    }
    assert(left == s->N);

    for (len = i, i = 0, j = 0; i < len; i ++) {
        if (i == 0) {
            buffer[j][3] = buffer[i][0];
            if (buffer[i][1] < buffer[i][2]) 
                buffer[j][4] = buffer[i][1];
            else 
                buffer[j][4] = buffer[i][2];
            j ++;
        }
        else {
            if (buffer[i - 1][1] < buffer[i - 1][2]) {
                if (buffer[i][1] <= buffer[i][2]) {
                    buffer[j][3] = buffer[i][0];
                    buffer[j][4] = buffer[i][1];
                    j ++;
                }
                else {
                    segments_intersect(
                        buffer[i - 1][0], buffer[i - 1][1], buffer[i - 1][2],
                        buffer[i][0], buffer[i][1], buffer[i][2], 
                        buffer[j] + 3, buffer[j] + 4);
                    j ++;
                    buffer[j][3] = buffer[i][0];
                    buffer[j][4] = buffer[i][2];
                    j ++;
                }
            }
            else {
                if (buffer[i][1] >= buffer[i][2]) {
                    buffer[j][3] = buffer[i][0];
                    buffer[j][4] = buffer[i][2];
                    j ++;
                }
                else {
                    segments_intersect(
                        buffer[i - 1][0], buffer[i - 1][1], buffer[i - 1][2],
                        buffer[i][0], buffer[i][1], buffer[i][2], 
                        buffer[j] + 3, buffer[j] + 4);
                    j ++;
                    buffer[j][3] = buffer[i][0];
                    buffer[j][4] = buffer[i][1];
                    j ++;
                }
            }
        }
    }

    for (len = j, i = len - 1; i >= 0; i --) {
        p->vertices[p->N] = new_vertex(
            buffer[i][3], buffer[i][4], p->N + 1);
        p->N ++;
    }
    p->L = p->N;
    for (i = p->N; i < p->M; i ++) 
        p->vertices[i] = NULL;
    
    p->external = NULL;
    structuralize(p);
    for (i = 0; i < s->N * 2; i ++) 
        free(buffer[i]);
    free(buffer);
    return p;
}

int sprint_check_simple_polygon(char *string_buffer, polytope *p) {
    int i, j;
    for (i = 0; i < p->N; i ++) {
        for (j = i + 2; j < p->N; j ++) {
            if (i == 0 && j == p->N - 1) continue;
            edge *e0 = p->vertices[i]->head;
            edge *e1 = p->vertices[j]->head;
            if (check_segments_touch(e0->from, e0->to, e1->from, e1->to)) {
                int len = sprintf(string_buffer, 
                    "edge intersection detected: ");
                len += sprint_edge(string_buffer + len, e0); 
                len += sprint_edge(string_buffer + len, e1);
                return len;
            }
        }
    }
    return sprintf(string_buffer, "simple polygon checked");
}

int traverse_polytope(polytope *p, facet **queue) {
    int head = 0, tail = 0;
    queue[tail ++] = p->external;
    p->external->visited = 1;
    while (head != tail) {
        facet *f = queue[head ++];
        edge *e = f->loop;
        do {
            assert(e->left_hand == f);
            facet *f0 = e->twin->left_hand;
            if (f0->visited == 0) {
                queue[tail ++] = f0;
                f0->visited = 1;
            }
            edge *temp = e;
            e = e->next;

        } while (e != f->loop);
    }
    return tail;
}

void free_polytope(polytope *p) {
    if (SHOW_DETAIL) {
        printf("     - %d vertices %d edges %d facets remain\n", 
            vertex_count[0], edge_count[0], facet_count[0 ]);
    }
    facet **queue = (facet **) get_buffer();
    int tail = traverse_polytope(p, queue);
    int i;
    for (i = 0; i < tail; i ++) {
        facet *f = queue[i];
        edge *e = f->loop;
        do {
            edge *temp = e;
            e = e->next;
            free_edge(temp);
        } while (e != f->loop);
        free_facet(f);
    }
    for (i = 0; i < p->M; i ++) {
        vertex *v = p->vertices[i];
        if (v != NULL) {
            free_vertex(v);
        }
    }
    free(p->vertices);
    free(p);
    if (SHOW_DETAIL) {
        printf("     - %d vertices %d edges %d facets allocated\n", 
            vertex_count[1], edge_count[1], facet_count[1]);
    }
    int len = sprintf(string_buffer, 
        "memory leak detected: %d vertices %d edges %d facets", 
        vertex_count[0], edge_count[0], facet_count[0]);
    handle_exception(
        vertex_count[0] == 0 && edge_count[0] == 0 && facet_count[0] == 0, 
        string_buffer);
    printf("   - polygon clear - %dms\n", clock() - START_TIME);
    START_TIME = clock();
    return_buffer((void **) queue);
}

void print_polytope(polytope *p) {
    facet **queue = (facet **) get_buffer();
    int tail = traverse_polytope(p, queue);
    int i;
    for (i = 0; i < tail; i ++) {
        print_facet(queue[i]);
        queue[i]->visited = 0;
    }
    printf("%d\n", tail);
    return_buffer((void **) queue);
}

void check_triangulation(polytope *p) {
    facet **queue = (facet **) get_buffer();
    int tail = traverse_polytope(p, queue);
    double S0 = -1, S1 = 0, minS = -1, maxS = -1;
    int i;
    for (i = 0; i < tail; i ++) {
        if (queue[i] != p->external) 
            assert(queue[i]->loop->next->next->next == queue[i]->loop);
        double A = area_of(queue[i]);
        if (S0 < 0 || -A > S0) S0 = -A;
        if (A > 0) S1 += A;
        if (minS < 0 || (A > 0 && A < minS)) minS = A;
        if (maxS < 0 || (A > 0 && A > maxS)) maxS = A;
        queue[i]->visited = 0;
    }
    if (SHOW_DETAIL) {
        printf("     - %d vertex searches and %d facet searches\n", 
            VERTEX_SEARCH_COUNT, FACET_SEARCH_COUNT);
        VERTEX_SEARCH_COUNT = FACET_SEARCH_COUNT = 0;
        printf("     - triangle size range = [%lf-%lf]\n", minS, maxS);
        printf("     - size diff = %lf - %lf = %lf\n", S0, S1, (S0 - S1));
    }
    printf("   - polygon triangulated - %dms\n", clock() - START_TIME);
    START_TIME = clock();
    int assertion = (tail - 1 == p->N - 2) 
        && (dabs(S0 - S1) <= S0 / (tail - 1));
    int len = sprintf(string_buffer, "triangulation failed: ");
    if (! assertion) {
        len = sprint_check_simple_polygon(string_buffer + len, p);
        handle_exception(
            string_buffer[strlen(string_buffer) - 1] == 'd', 
            string_buffer);
        // ^^^ this O(n^2) procedure could be skipped
    }
    handle_exception(assertion, string_buffer);
    return_buffer((void **) queue);
}

void append_to_vertices(polytope *p, vertex *v) {
    p->vertices[p->L ++] = v;
    v->id = p->L;
}

int sprintf_overlap(char *string_buffer, vertex *a, vertex *b) {
    int len = sprintf(string_buffer, "vertex overlap detected: ");
    len += sprint_vertex(string_buffer + len, a);
    len += sprint_vertex(string_buffer + len, b);
    return len;
}

int type_of(vertex *b) {
    vertex *a, *c;
    a = b->in->from;
    c = b->out->to;
    int da = compare_point_cartesian(a, b), 
        dc = compare_point_cartesian(c, b);
    sprintf_overlap(string_buffer, a, b);
    handle_exception(da != 0, string_buffer);
    sprintf_overlap(string_buffer, c, b);
    handle_exception(dc != 0, string_buffer);
    double ac = cross(b, a, b, c);
    if (da == 1 && dc == 1) {
        sprintf_overlap(string_buffer, a, c);
        handle_exception(ac != 0, string_buffer);
        if (ac < 0) return 0; // END
        if (ac > 0) return 1; // MERGE
    }
    if (da == -1 && dc == -1) {
        sprintf_overlap(string_buffer, a, c);
        handle_exception(ac != 0, string_buffer);
        if (ac > 0) return 2; // SPLIT
        if (ac < 0) return 3; // START
    }
    if (da == 1 && dc == -1) return 4; // DOWN
    if (da == -1 && dc == 1) return 5; // UP
}

char TYPE[6][6] = {"END", "MERGE", "SPLIT", "START", "DOWN", "UP"};

int between(edge *e0, edge *e1, edge *e2) {
    double c12 = cross(e1->from, e1->to, e2->from, e2->to);
    double c10 = cross(e1->from, e1->to, e0->from, e0->to);
    double c02 = cross(e0->from, e0->to, e2->from, e2->to);
    if (sgn(c12) == 0) return -1;
    if (c12 > 0)
        return c10 > 0 && c02 > 0;
    else
        return c10 > 0 || c02 > 0;
    return 0;
}

edge *match_edge(vertex *v1, vertex *v2);

edge *connect_vertices(vertex *v1, vertex *v2, facet *internal) {
    edge *e0 = new_edge();
    edge *e1 = new_edge();
    e0->twin = e1;
    e1->twin = e0;
    e0->from = v1; e0->to = v2;
    e1->from = v2; e1->to = v1;
    edge *ei, *ej, *ek;
    
    ei = v1->head;
    do {
        VERTEX_SEARCH_COUNT ++;
        if (ei->left_hand == internal) break;
        ei = ei->prev->twin;
    } while (ei != v1->head);
    ej = v2->head;
    do {
        VERTEX_SEARCH_COUNT ++;
        if (ej->left_hand == internal) break;
        ej = ej->prev->twin;
    } while (ej != v2->head);
    assert(ei->left_hand == internal);
    assert(ej->left_hand == internal);

    ej->prev->next = e1;
    e1->prev = ej->prev;
    ei->prev->next = e0;
    e0->prev = ei->prev;

    e0->next = ej;
    ej->prev = e0;
    e1->next = ei;
    ei->prev = e1;

    facet *f0 = ei->left_hand;
    facet *f1 = new_facet();
    if (ei->next->to == v2) {
        e0->left_hand = f0;
        e1->left_hand = f1;
        f0->loop = e0;
        f1->loop = e1;
        for (ek = ei; ek->from != v2; ek = ek->next) {
            FACET_SEARCH_COUNT ++;
            assert(ek->left_hand == f0);
            ek->left_hand = f1;
        }
        return e0;
    }
    else {
        e0->left_hand = f1;
        e1->left_hand = f0;
        f0->loop = e1;
        f1->loop = e0;
        for (ek = ej; ek->from != v1; ek = ek->next) {
            FACET_SEARCH_COUNT ++;
            assert(ek->left_hand == f0);
            ek->left_hand = f1;
        }
        return e1;
    }
}

edge *connect_vertices_2(vertex *v1, vertex *v2, facet *internal) {
    edge *e0 = new_edge();
    edge *e1 = new_edge();
    e0->twin = e1;
    e1->twin = e0;
    e0->from = v1; e0->to = v2;
    e1->from = v2; e1->to = v1;
    edge *ei, *ej, *ek;
    
    ei = v1->head;
    do {
        VERTEX_SEARCH_COUNT ++;
        if (ei->left_hand == internal) break;
        ei = ei->prev->twin;
    } while (ei != v1->head);
    ej = v2->head;
    do {
        VERTEX_SEARCH_COUNT ++;
        if (ej->left_hand == internal) break;
        ej = ej->prev->twin;
    } while (ej != v2->head);
    assert(ei->left_hand == internal);
    assert(ej->left_hand == internal);
    
    ej->prev->next = e1;
    e1->prev = ej->prev;
    ei->prev->next = e0;
    e0->prev = ei->prev;

    e0->next = ej;
    ej->prev = e0;
    e1->next = ei;
    ei->prev = e1;

    facet *f0 = ei->left_hand;
    facet *f1 = new_facet();
    if (ei->next->to == v2) {
        e0->left_hand = f0;
        e1->left_hand = f1;
        f0->loop = e0;
        f1->loop = e1;
        for (ek = ei; ek->from != v2; ek = ek->next) {
            FACET_SEARCH_COUNT ++;
            assert(ek->left_hand == f0);
            ek->left_hand = f1;
        }
        return e0;
    }
    else {
        e0->left_hand = f1;
        e1->left_hand = f0;
        f0->loop = e1;
        f1->loop = e0;
        for (ek = ej; ek->from != v1; ek = ek->next) {
            FACET_SEARCH_COUNT ++;
            assert(ek->left_hand == f0);
            ek->left_hand = f1;
        }
        return e0;
    }
}

edge *connect_vertices_3(
    vertex *v1, vertex *v2, facet *internal, edge *ev1, edge *ev2) 
{
    edge *e0 = new_edge();
    edge *e1 = new_edge();
    e0->twin = e1;
    e1->twin = e0;
    e0->from = v1; e0->to = v2;
    e1->from = v2; e1->to = v1;
    edge *ei, *ej, *ek;
    
    if (ev1 != NULL) {
        assert(ev1->from == v1);
        ei = ev1;
    }
    else 
        ei = v1->head;
    do {
        VERTEX_SEARCH_COUNT ++;
        if (ei->left_hand == internal) break;
        ei = ei->prev->twin;
    } while (ei != v1->head);
    if (ev2 != NULL) {
        assert(ev2->from == v2);
        ej = ev2;
    }
    else 
        ej = v2->head;
    do {
        VERTEX_SEARCH_COUNT ++;
        if (ej->left_hand == internal) break;
        ej = ej->prev->twin;
    } while (ej != v2->head);
    assert(ei->left_hand == internal);
    assert(ej->left_hand == internal);
    
    ej->prev->next = e1;
    e1->prev = ej->prev;
    ei->prev->next = e0;
    e0->prev = ei->prev;

    e0->next = ej;
    ej->prev = e0;
    e1->next = ei;
    ei->prev = e1;

    facet *f0 = ei->left_hand;
    facet *f1 = new_facet();
    if (ei->next->to == v2) {
        e0->left_hand = f0;
        e1->left_hand = f1;
        f0->loop = e0;
        f1->loop = e1;
        for (ek = ei; ek->from != v2; ek = ek->next) {
            FACET_SEARCH_COUNT ++;
            assert(ek->left_hand == f0);
            ek->left_hand = f1;
        }
        return e0;
    }
    else {
        e0->left_hand = f1;
        e1->left_hand = f0;
        f0->loop = e1;
        f1->loop = e0;
        for (ek = ej; ek->from != v1; ek = ek->next) {
            FACET_SEARCH_COUNT ++;
            assert(ek->left_hand == f0);
            ek->left_hand = f1;
        }
        return e0;
    }
}

void disconnect_vertices(edge *e0) {
    edge *e1 = e0->twin;
    facet *f0 = e0->left_hand, *f1 = e1->left_hand;
    if (f0->loop == e0) 
        f0->loop = e0->next;
    edge *e = e1->next;
    while (e != e1) {
        e->left_hand = f0;
        e = e->next;
    }
    e1->prev->next = e0->next;
    e0->next->prev = e1->prev;
    e1->next->prev = e0->prev;
    e0->prev->next = e1->next;
    free_edge(e0);
    free_edge(e1);
    free_facet(f1);
}

int sprintf_disorder(char *string_buffer, vertex *a, vertex *b) {
    int len = sprintf(string_buffer, "non-monotone polygon detected: ");
    len += sprint_vertex(string_buffer + len, a);
    len += sprint_vertex(string_buffer + len, b);
    return len;
}

void triangulate_monotone(facet *f) {
    edge *start = NULL, *end = NULL;
    edge *e = f->loop;
    do {
        if (start == NULL || 
        compare_point_cartesian(e->from, start->from) == 1)
            start = e;
        if (end == NULL || 
        compare_point_cartesian(end->from, e->from) == 1)
            end = e;
        e = e->next;
    } while (e != f->loop);
    edge *left = start, *right = start->prev;
    vertex **queue = (vertex **) get_buffer();
    int head = 0, tail = 0;
    start->from->side = 3;
    queue[tail ++] = start->from;
    while (left->to != end->from && right->from != end->from) {
        /*
        sprintf_disorder(string_buffer, left->to, left->next->to);
        handle_exception(
            compare_point_cartesian(left->to, left->next->to) == 1, 
            string_buffer);
        sprintf_disorder(string_buffer, right->from, right->prev->from);
        handle_exception(
            compare_point_cartesian(right->from, right->prev->from) == 1, 
            string_buffer);
        */
        if (left->to->y > right->from->y) {
            left->to->side = 1;
            queue[tail ++] = left->to;
            left = left->next;
        }
        else {
            right->from->side = 2;
            queue[tail ++] = right->from;
            right = right->prev;
        }
    }
    while (left->to != end->from) {
        /*
        sprintf_disorder(string_buffer, left->to, left->next->to);
        handle_exception(
            compare_point_cartesian(left->to, left->next->to) == 1, 
            string_buffer);
        */
        left->to->side = 1;
        queue[tail ++] = left->to;
        left = left->next;
    }
    while (right->from != end->from) {
        /*
        sprintf_disorder(string_buffer, right->from, right->prev->from);
        handle_exception(
            compare_point_cartesian(right->from, right->prev->from) == 1, 
            string_buffer);
        */
        right->from->side = 2;
        queue[tail ++] = right->from;
        right = right->prev;
    }
    end->from->side = 3;
    queue[tail ++] = end->from;
    vertex **stack = (vertex **) get_buffer();
    int top = 0;
    stack[top ++] = queue[0];
    stack[top ++] = queue[1];
    int i;
    for (i = 2; i < tail - 1; i ++) {
        //assert(top > 0);
        if (stack[top - 1]->side != queue[i]->side) {
            int j;
            for (j = 1; j < top; j ++) 
                connect_vertices_2(queue[i], stack[j], f);
            top = 0;
            //assert(i - 1 > 0);
            stack[top ++] = queue[i - 1];
            stack[top ++] = queue[i];
        }
        else {
            vertex *v = stack[-- top], *u;
            while (top != 0 && (
            (queue[i]->side == 1 && 
                cross(stack[top - 1], v, v, queue[i]) > 0) ||
            (queue[i]->side == 2 && 
                cross(stack[top - 1], v, v, queue[i]) < 0))) 
            {
                u = stack[-- top];
                connect_vertices_2(queue[i], u, f);
                v = u;
            }
            stack[top ++] = v;
            stack[top ++] = queue[i];
        }
    }
    -- top;
    int j;
    for (j = 1; j < top; j ++)
        connect_vertices_2(queue[tail - 1], stack[j], f);
    top = 0;
    return_buffer((void **) queue);
    return_buffer((void **) stack);
}

void triangulate_facet(facet *f) {
    // can be a complicated linear algorithm
    // but as efficient in practice\
    where facets re-triangulated are small
    vertex **queue = (vertex **) get_buffer();
    facet **stack = (facet **) get_buffer();
    int tail = 0, top = 0;
    edge *e = f->loop;
    do {
        e->from->out = e;
        e->to->in = e;
        queue[tail ++] = e->from;
        e->helper = NULL;
        e = e->next;
    } while (e != f->loop);
    sort_by_cartesian(queue, 0, tail - 1);
    bst_node *root = BST_NULL;
    stack[top ++] = f;
    int i;
    for (i = 0; i < tail; i ++) {
        vertex *v =  queue[i];
        switch (type_of(v)) {
            case 0: // END
                if (type_of(v->in->helper) == 1) // MERGE
                    stack[top ++] = connect_vertices(v, v->in->helper, 
                        v->in->left_hand)->twin->left_hand;
                root = bst_delete(root, v->in, v->y);
                v->in->helper = NULL;
                break;
            case 1: // MERGE
                if (type_of(v->in->helper) == 1) // MERGE
                    stack[top ++] = connect_vertices(v, v->in->helper, 
                        v->in->left_hand)->twin->left_hand;
                root = bst_delete(root, v->in, v->y);
                v->in->helper = NULL;
                bst_node *temp = search_prec(root, v->x, v->y);
                if (type_of(temp->e->helper) == 1) // MERGE
                    stack[top ++] = connect_vertices(v, temp->e->helper, 
                        temp->e->left_hand)->twin->left_hand;
                temp->e->helper = v;
                break;
            case 2: // SPLIT
                temp = search_prec(root, v->x, v->y);
                stack[top ++] = connect_vertices(v, temp->e->helper, 
                    temp->e->left_hand)->twin->left_hand;
                temp->e->helper = v;
                root = bst_insert(root, v->out, v->y);
                v->out->helper = v;
                break;
            case 3: // START
                root = bst_insert(root, v->out, v->y);
                v->out->helper = v;
                break;
            case 4: // DOWN
                if (type_of(v->in->helper) == 1) // MERGE
                    stack[top ++] = connect_vertices(v, v->in->helper, 
                        v->in->left_hand)->twin->left_hand;
                root = bst_delete(root, v->in, v->y);
                v->in->helper = NULL;
                root = bst_insert(root, v->out, v->y);
                v->out->helper = v;
                break;
            case 5: // UP
                temp = search_prec(root, v->x, v->y);
                if (type_of(temp->e->helper) == 1) // MERGE
                    stack[top ++] = connect_vertices(v, temp->e->helper, 
                        temp->e->left_hand)->twin->left_hand;
                temp->e->helper = v;
                break;
            default: ;
        }
        //print_bst(root, v->y); printf("\n");
    }
    assert(root == BST_NULL);
    for (i = 0; i < tail; i ++) {
        assert(queue[i]->out->helper == NULL);
        queue[i]->in = queue[i]->out = NULL;
    }
    if (MONOTONE_ONLY) 
        assert(top == 1);
    while (top > 0) {
        //print_facet(stack[top - 1]);
        facet *f = stack[-- top];
        triangulate_monotone(f);
    }
    return_buffer((void **)  queue);
    return_buffer((void **)  stack);
}

void triangulate_polygon(polytope *p) {
    facet *internal = p->external->loop->twin->left_hand;
    //use triangulate_facet to compute the link distance\
    if p is not a tube
    if (MONOTONE_ONLY) 
        triangulate_monotone(internal);
    else 
        triangulate_facet(internal);
    check_triangulation(p);
}

void print_funnel(funnel *fn) {
    vertex **stack = (vertex **) get_buffer();
    printf("[ ");
    chain_node *cn;
    for (cn = fn->left_chain; cn != NULL; cn = cn->next) 
        printf("%d ", cn->v->id);
    printf("(%d) ", fn->apex->id);
    int top = 0;
    for (cn = fn->right_chain; cn != NULL; cn = cn->next) 
        stack[top ++] = cn->v;
    while (top > 0) 
        printf("%d ", stack[-- top]->id);
    printf("]\n");
    return_buffer((void **) stack);
}

funnel *new_funnel(vertex *v) {
    funnel *fn = (funnel *) malloc(sizeof(funnel));
    funnel_count[0] ++;
    funnel_count[1] ++;
    fn->apex = v;
    fn->left_chain = fn->right_chain = NULL;
    return fn;
}

chain_node *new_chain_node(vertex *v) {
    chain_node *cn = (chain_node *) malloc(sizeof(chain_node));
    chain_node_count[0] ++;
    chain_node_count[1] ++;
    cn->v = v;
    cn->next = NULL;
    return cn;
}

void free_funnel(funnel *fn) {
    chain_node *cn, *prev_cn;
    for (prev_cn = NULL, cn = fn->left_chain; cn != NULL; 
        prev_cn = cn, cn = cn->next, 
        free(prev_cn), chain_node_count[0] --);
    for (prev_cn = NULL, cn = fn->right_chain; cn != NULL; 
        prev_cn = cn, cn = cn->next, 
        free(prev_cn), chain_node_count[0] --);
    free(fn);
    funnel_count[0] --;
}

vertex *left_end(funnel *fn) {
    if (fn->left_chain == NULL) 
        return fn->apex;
    else 
        return fn->left_chain->v;
}

vertex *right_end(funnel *fn) {
    if (fn->right_chain == NULL) 
        return fn->apex;
    else 
        return fn->right_chain->v;
}

void link_to_parent(vertex *v0, vertex *v1, int i) {
    v1->sp[i]->parent = v0;
    v1->sp[i]->depth = v0->sp[i]->depth + 1;
    if (v0->sp[i]->parent == NULL) {
        v1->sp[i]->cross = 0;
        v1->sp[i]->convex = 3;
    }
    else {
        v1->sp[i]->cross = cross(v0->sp[i]->parent, v0, v0, v1);
        switch (sgn(v1->sp[i]->cross)) {
            case 0: 
                v1->sp[i]->convex = v0->sp[i]->convex & 3;
                break;
            case 1: 
                v1->sp[i]->convex = v0->sp[i]->convex & 2;
                break;
            case -1: 
                v1->sp[i]->convex = v0->sp[i]->convex & 1;
                break;
            default: 
                assert(0);
                break;
        }
    }
}

void depth_first_traverse(polytope *p, edge *e, funnel *fn) {
    facet *f = e->left_hand;
    if (f == p->external) return ;
    assert(e->next->next->next == e);
    vertex *v = e->next->to;
    if (fn->left_chain == NULL) {
        assert(fn->right_chain != NULL);
        assert(fn->right_chain->next == NULL);
        assert(e->from == fn->apex);
        assert(e->to == fn->right_chain->v);
        link_to_parent(fn->apex, v, 0);
        funnel *fn0 = new_funnel(fn->apex);
        fn0->right_chain = new_chain_node(v);
        depth_first_traverse(p, e->prev->twin, fn0);
        free_funnel(fn0);
        fn->left_chain = new_chain_node(v);
        depth_first_traverse(p, e->next->twin, fn);
    }
    else if (fn->right_chain == NULL) {
        assert(fn->left_chain != NULL);
        assert(fn->left_chain->next == NULL);
        assert(e->from == fn->left_chain->v);
        assert(e->to == fn->apex);
        link_to_parent(fn->apex, v, 0);
        fn->right_chain = new_chain_node(v);
        depth_first_traverse(p, e->prev->twin, fn);
        funnel *fn0 = new_funnel(fn->apex);
        fn0->left_chain = new_chain_node(v);
        depth_first_traverse(p, e->next->twin, fn0);
        free_funnel(fn0);
    }
    else {
        chain_node *prev_cn, *cn;
        for (prev_cn = NULL, cn = fn->left_chain; cn != NULL; 
            prev_cn = cn, cn = cn->next) 
        {
            double cr;
            if (cn->next == NULL) 
                cr = cross(fn->apex, cn->v, cn->v, v);
            else 
                cr = cross(cn->next->v, cn->v, cn->v, v);
            if (cr >= 0) break;
        }
        if (cn == NULL) {
            for (prev_cn = NULL, cn = fn->right_chain; cn != NULL; 
            prev_cn = cn, cn = cn->next) 
            {
                double cr;
                if (cn->next == NULL) 
                    cr = cross(fn->apex, cn->v, cn->v, v);
                else 
                    cr = cross(cn->next->v, cn->v, cn->v, v);
                if (cr <= 0) break;
            }
            if (cn == NULL) {
                link_to_parent(fn->apex, v, 0);
                funnel *fn0 = new_funnel(fn->apex);
                fn0->left_chain = fn->left_chain;
                fn0->right_chain = new_chain_node(v);
                depth_first_traverse(p, e->prev->twin, fn0);
                free_funnel(fn0);
                fn->left_chain = new_chain_node(v);
                depth_first_traverse(p, e->next->twin, fn);
            }
            else {
                link_to_parent(cn->v, v, 0);
                funnel *fn0 = new_funnel(cn->v);
                if (prev_cn == NULL) 
                    fn0->right_chain = NULL;
                else {
                    fn0->right_chain = fn->right_chain;
                    prev_cn->next = NULL;
                }
                fn0->left_chain = new_chain_node(v);
                depth_first_traverse(p, e->next->twin, fn0);
                free_funnel(fn0);
                fn->right_chain = new_chain_node(v);
                fn->right_chain->next = cn;
                depth_first_traverse(p, e->prev->twin, fn); 
            }
        }
        else {
            link_to_parent(cn->v, v, 0);
            funnel *fn0 = new_funnel(cn->v);
            if (prev_cn == NULL) 
                fn0->left_chain = NULL;
            else {
                fn0->left_chain = fn->left_chain;
                prev_cn->next = NULL;
            }
            fn0->right_chain = new_chain_node(v);
            depth_first_traverse(p, e->prev->twin, fn0);
            free_funnel(fn0);
            fn->left_chain = new_chain_node(v);
            fn->left_chain->next = cn;
            depth_first_traverse(p, e->next->twin, fn);
        }
    }
}

void print_path(vertex *v, int i) {
    vertex **stack = (vertex **) get_buffer();
    int top = 0;
    for ( ; v != NULL; v = v->sp[i]->parent) 
        stack[top ++] = v;
    while (top > 0) {
        v = stack[-- top];
        printf("> %d (%d) (%lf) ", v->sp[i]->convex, 
            sgn(v->sp[i]->cross), v->sp[i]->cross);
    }
    printf(">\n");
    return_buffer((void **) stack);
}

void print_shortest_path(polytope *p, vertex *source, int index) {
    vertex **stack = (vertex **) get_buffer();
    int i;
    for (i = 0; i < p->N; i ++) {
        vertex *v = p->vertices[i];
        int top = 0;
        for (v = p->vertices[i]; v != NULL; v = v->sp[index]->parent) 
            stack[top ++] = v;
        assert(top == 1 || stack[top - 1] == source);
        while (top > 0) {
            v = stack[-- top];
            printf("> %d ", v->id);
        }
        printf(">\n");
    }
    return_buffer((void **) stack);
}

void set_source(vertex *v, int i) {
    v->sp[i]->parent = NULL;
    v->sp[i]->cross = 0;
    v->sp[i]->convex = 3;
    v->sp[i]->depth = 0;
}

void shortest_path_from(polytope *p, vertex *source) {
    set_source(source, 0);
    edge *e = source->head;
    link_to_parent(source, e->to, 0);
    funnel *fn = new_funnel(source);
    fn->right_chain = new_chain_node(e->to);
    depth_first_traverse(p, e, fn);
    free_funnel(fn);
    print_shortest_path(p, source, 0);
}

void shortest_path_from_all(polytope *p) {
    int i;
    double j = 0;
    for (i = 0; i < p->N; i ++) {
        shortest_path_from(p, p->vertices[i]);
        if ((double) (i + 1) / p->N > j) {j += 0.05; printf(".");}
    }
    printf("\n - paths computed - %dms\n", clock() - START_TIME);
    START_TIME = clock();
}

window *new_window(
    polytope *p, vertex *v0, vertex *v1, 
    edge *e0, edge *e1) 
{
    window *w = (window *) malloc(sizeof(window));
    window_count ++;
    w->p = p;
    w->v0 = v0; w->v1 = v1;
    w->e0 = e0; w->e1 = e1;
    w->depth = - INF;
    w->parent = NULL;
    return w;
}

void free_window(window *w) {
    free(w);
    window_count --;
}

edge *match_edge(vertex *v0, vertex *v1);

void cache_window(polytope *p, 
    vertex *v0, vertex *v1, edge *e0, edge *e1, 
    window **queue, int *tail, int to_split)
{
    if (queue != NULL) {
        window *w = new_window(p, v0, v1, e0, e1);
        queue[(* tail) ++] = w;
        w->to_split = to_split;
    }
}

int bi_depth_first_traverse(polytope *p, 
    edge *e, funnel *fn0, funnel *fn1, 
    window **queue, int *tail) 
{
    /*
    assert(left_end(fn0) == e->from 
        && right_end(fn0) == e->to);
    assert(left_end(fn1) == e->from 
        && right_end(fn1) == e->to);
    */
    int ret = 0;
    chain_node *prev_cn, *cn;
    vertex *tan[2][2];
    tan[0][0] = fn0->apex;
    tan[1][1] = fn1->apex;
    for (prev_cn = NULL, cn = fn0->right_chain; cn != NULL; 
        prev_cn = cn, cn = cn->next);
    if (prev_cn == NULL) 
        tan[1][0] = fn0->apex;
    else 
        tan[1][0] = prev_cn->v;
    for (prev_cn = NULL, cn = fn1->left_chain; cn != NULL; 
        prev_cn = cn, cn = cn->next);
    if (prev_cn == NULL) 
        tan[0][1] = fn1->apex;
    else 
        tan[0][1] = prev_cn->v;
    if (e != e->next->next->next) 
        return ;
    
    vertex *v = e->next->to;
    funnel *fn0_new = NULL, *fn1_new = NULL;
    int order0 = -1, order1 = -1;
    if (fn0->left_chain == NULL) {
        /*
        assert(fn0->right_chain != NULL);
        assert(fn0->right_chain->next == NULL);
        */
        link_to_parent(fn0->apex, v, 0);
        fn0_new = new_funnel(fn0->apex);
        fn0_new->right_chain = new_chain_node(v);
        //depth_first_traverse(p, e->prev->twin, fn0_new);
        //free_funnel(fn0_new);
        fn0->left_chain = new_chain_node(v);
        //depth_first_traverse(p, e->next->twin, fn0);
        order0 = 0;
    }
    else if (fn0->right_chain == NULL) {
        /*
        assert(fn0->left_chain != NULL);
        assert(fn0->left_chain->next == NULL);
        */
        link_to_parent(fn0->apex, v, 0);
        fn0->right_chain = new_chain_node(v);
        //depth_first_traverse(p, e->prev->twin, fn0);
        fn0_new = new_funnel(fn0->apex);
        fn0_new->left_chain = new_chain_node(v);
        //depth_first_traverse(p, e->next->twin, fn0_new);
        //free_funnel(fn0_new);
        order0 = 1;
    }
    else {
        for (prev_cn = NULL, cn = fn0->left_chain; cn != NULL; 
            prev_cn = cn, cn = cn->next) 
        {
            double cr;
            if (cn->next == NULL) 
                cr = cross(fn0->apex, cn->v, cn->v, v);
            else 
                cr = cross(cn->next->v, cn->v, cn->v, v);
            if (cr >= 0) break;
        }
        if (cn == NULL) {
            for (prev_cn = NULL, cn = fn0->right_chain; cn != NULL; 
                prev_cn = cn, cn = cn->next) 
            {
                double cr;
                if (cn->next == NULL) 
                    cr = cross(fn0->apex, cn->v, cn->v, v);
                else 
                    cr = cross(cn->next->v, cn->v, cn->v, v);
                if (cr <= 0) break;
            }
            if (cn == NULL) {
                link_to_parent(fn0->apex, v, 0);
                fn0_new = new_funnel(fn0->apex);
                fn0_new->left_chain = fn0->left_chain;
                fn0_new->right_chain = new_chain_node(v);
                //depth_first_traverse(p, e->prev->twin, fn0_new);
                //free_funnel(fn0_new);
                fn0->left_chain = new_chain_node(v);
                //depth_first_traverse(p, e->next->twin, fn0);
                order0 = 0;
            }
            else {
                link_to_parent(cn->v, v, 0);
                fn0_new = new_funnel(cn->v);
                if (prev_cn == NULL) 
                    fn0_new->right_chain = NULL;
                else {
                    fn0_new->right_chain = fn0->right_chain;
                    prev_cn->next = NULL;
                }
                fn0_new->left_chain = new_chain_node(v);
                //depth_first_traverse(p, e->next->twin, fn0_new);
                //free_funnel(fn0_new);
                fn0->right_chain = new_chain_node(v);
                fn0->right_chain->next = cn;
                //depth_first_traverse(p, e->prev->twin, fn0);
                order0 = 1;
            }
        }
        else {
            link_to_parent(cn->v, v, 0);
            fn0_new = new_funnel(cn->v);
            if (prev_cn == NULL) 
                fn0_new->left_chain = NULL;
            else {
                fn0_new->left_chain = fn0->left_chain;
                prev_cn->next = NULL;
            }
            fn0_new->right_chain = new_chain_node(v);
            //depth_first_traverse(p, e->prev->twin, fn0_new);
            //free_funnel(fn0_new);
            fn0->left_chain = new_chain_node(v);
            fn0->left_chain->next = cn;
            //depth_first_traverse(p, e->next->twin, fn0);
            order0 = 0;
        }
    }
    
    if (fn1->left_chain == NULL) {
        /*
        assert(fn1->right_chain != NULL);
        assert(fn1->right_chain->next == NULL);
        */
        link_to_parent(fn1->apex, v, 1);
        fn1_new = new_funnel(fn1->apex);
        fn1_new->right_chain = new_chain_node(v);
        //depth_first_traverse(p, e->prev->twin, fn1_new);
        //free_funnel(fn1_new);
        fn1->left_chain = new_chain_node(v);
        //depth_first_traverse(p, e->next->twin, fn1);
        order1 = 0;
    }
    else if (fn1->right_chain == NULL) {
        /*
        assert(fn1->left_chain != NULL);
        assert(fn1->left_chain->next == NULL);
        */
        link_to_parent(fn1->apex, v, 1);
        fn1->right_chain = new_chain_node(v);
        //depth_first_traverse(p, e->prev->twin, fn1);
        fn1_new = new_funnel(fn1->apex);
        fn1_new->left_chain = new_chain_node(v);
        //depth_first_traverse(p, e->next->twin, fn1_new);
        //free_funnel(fn1_new);
        order1 = 1;
    }
    else {
        for (prev_cn = NULL, cn = fn1->left_chain; cn != NULL;
            prev_cn = cn, cn = cn->next) 
        {
            double cr;
            if (cn->next == NULL) 
                cr = cross(fn1->apex, cn->v, cn->v, v);
            else 
                cr = cross(cn->next->v, cn->v, cn->v, v);
            if (cr >= 0) break;
        }
        if (cn == NULL) {
            for (prev_cn = NULL, cn = fn1->right_chain; cn != NULL; 
                prev_cn = cn, cn = cn->next) 
            {
                double cr;
                if (cn->next == NULL) 
                    cr = cross(fn1->apex, cn->v, cn->v, v);
                else 
                    cr = cross(cn->next->v, cn->v, cn->v, v);
                if (cr <= 0) break;
            }
            if (cn == NULL) {
                link_to_parent(fn1->apex, v, 1);
                fn1_new = new_funnel(fn1->apex);
                fn1_new->left_chain = fn1->left_chain;
                fn1_new->right_chain = new_chain_node(v);
                //depth_first_traverse(p, e->prev->twin, fn1_new);
                //free_funnel(fn1_new);
                fn1->left_chain = new_chain_node(v);
                //depth_first_traverse(p, e->next->twin, fn1);
                order1 = 0;
            }
            else {
                link_to_parent(cn->v, v, 1);
                fn1_new = new_funnel(cn->v);
                if (prev_cn == NULL) 
                    fn1_new->right_chain = NULL;
                else {
                    fn1_new->right_chain = fn1->right_chain;
                    prev_cn->next = NULL;
                }
                fn1_new->left_chain = new_chain_node(v);
                //depth_first_traverse(p, e->next->twin, fn1_new);
                //free_funnel(fn1_new);
                fn1->right_chain = new_chain_node(v);
                fn1->right_chain->next = cn;
                //depth_first_traverse(p, e->prev->twin, fn1);
                order1 = 1;
            }
        }
        else {
            link_to_parent(cn->v, v, 1);
            fn1_new = new_funnel(cn->v);
            if (prev_cn == NULL) 
                fn1_new->left_chain = NULL;
            else {
                fn1_new->left_chain = fn1->left_chain;
                prev_cn->next = NULL;
            }
            fn1_new->right_chain = new_chain_node(v);
            //depth_first_traverse(p, e->prev->twin, fn1_new);
            //free_funnel(fn1_new);
            fn1->left_chain = new_chain_node(v);
            fn1->left_chain->next = cn;
            //depth_first_traverse(p, e->next->twin, fn1);
            order1 = 0;
        }
    }

    funnel *fn[2][2];
    if (order0 == 0) {
        if (order1 == 0) {
            fn[0][0] = fn0_new; fn[0][1] = fn1_new;
            fn[1][0] = fn0; fn[1][1] = fn1;
        }
        else if (order1 == 1) {
            fn[0][0] = fn0_new; fn[0][1] = fn1;
            fn[1][0] = fn0; fn[1][1] = fn1_new;
        }
        else assert(0);
    }
    else if (order0 == 1){
        if (order1 == 0) {
            fn[0][0] = fn0; fn[0][1] = fn1_new;
            fn[1][0] = fn0_new; fn[1][1] = fn1;
        }
        else if (order1 == 1) {
            fn[0][0] = fn0; fn[0][1] = fn1;
            fn[1][0] = fn0_new; fn[1][1] = fn1_new;
        }
        else assert(0);
    }
    else assert(0);

    if ((e->from->sp[0]->convex & 2) > 0 && 
        (v->sp[1]->convex & 1) > 0) 
    {
        edge *e0 = e->prev->twin;
        if (e0->left_hand != p->external) 
            ret = ret | bi_depth_first_traverse(
                p, e0, fn[0][0], fn[0][1], queue, tail);
        else {
            vertex *l0 = segment_line_intersect(
                e0->from, e0->to, tan[1][1], tan[0][1]);
            vertex *l1 = segment_line_intersect(
                e0->from, e0->to, tan[0][0], tan[1][0]);
            assert(l0 != NULL);
            // tan[0][1] - l0 = v
            if (tan[0][1] != l0) {
                int to_split = 0;
                if (l0 != e0->from && l0 != e0->to) {
                    append_to_vertices(p, l0);
                    to_split = 1;
                }
                cache_window(
                    p, tan[0][1], l0, NULL, e0, 
                    queue, tail, to_split);
                if (last_win == NULL && e->prev == DESTINATION) {
                    ret = 1;
                    last_win = new_window(p, queue[*tail - 1]->v0, queue[*tail - 1]->v1, NULL, NULL);
                }
            }
            else {
                if (last_win == NULL && e->prev == DESTINATION) {
                    ret = 1;
                    last_win = new_window(p, tan[0][1], tan[1][1], NULL, NULL);
                }
            }
            if (l1 != NULL) {
                // tan[0][1] - l0 = l1 - tan[1][0]
                if (l1 != tan[1][0]) {
                    int to_split = 0;
                    if (l1 != e0->from && l1 != e0->to) {
                        append_to_vertices(p, l1);
                        to_split = 1;
                    }
                    cache_window(
                        p, l1, tan[1][0], e0, NULL, 
                        queue, tail, to_split);
                }
            }
        }
    }

    if ((v->sp[0]->convex & 2) > 0 && 
        (e->to->sp[1]->convex & 1) > 0) 
    {
        edge *e1 = e->next->twin;
        if (e1->left_hand != p->external) 
            ret = ret | bi_depth_first_traverse(
                p, e1, fn[1][0], fn[1][1], queue, tail);
        else {
            vertex *r0 = segment_line_intersect(
                e1->from, e1->to, tan[1][1], tan[0][1]);
            vertex *r1 = segment_line_intersect(
                e1->from, e1->to, tan[0][0], tan[1][0]);
            if (r0 != NULL) {
                // tan[0][1] - r0 = r1 - tan[1][0]
                if (tan[0][1] != r0) {
                    int to_split = 0;
                    if (r0 != e1->from && r0 != e1->to) {
                        append_to_vertices(p, r0);
                        to_split = 1;
                    }
                    cache_window(
                        p, tan[0][1], r0, NULL, e1, 
                        queue, tail, to_split);
                }
            }
            assert(r1 != NULL);
            // v = r1 - tan[1][0]
            if (r1 != tan[1][0]) {
                int to_split = 0;
                if (r1 != e1->from && r1 != e1->to) {
                    append_to_vertices(p, r1);
                    to_split = 1;
                }
                cache_window(
                    p, r1, tan[1][0], e1, NULL, 
                    queue, tail, to_split);
                if (last_win == NULL && e->next == DESTINATION) {
                    ret = 1;
                    last_win = new_window(p, queue[*tail - 1]->v0, queue[*tail - 1]->v1, NULL, NULL);
                }
            }
            else {
                if (last_win == NULL && e->next == DESTINATION) {
                    ret = 1;
                    last_win = new_window(p, tan[1][0], tan[0][0], NULL, NULL);
                }
            }
        }
    }
    free_funnel(fn0_new);
    free_funnel(fn1_new);
    return ret;
}

void bi_shortest_path_from(polytope *p, vertex *s0, vertex *s1) {
    set_source(s0, 0);
    set_source(s1, 1);
    edge *e = s0->head;
    assert(e->from == s0 && e->to == s1);
    link_to_parent(s0, s1, 0);
    funnel *fn0 = new_funnel(s0);
    fn0->right_chain = new_chain_node(s1);
    link_to_parent(s1, s0, 1);
    funnel *fn1 = new_funnel(s1);
    fn1->left_chain = new_chain_node(s0);
    bi_depth_first_traverse(p, e, fn0, fn1, NULL, NULL);
    free_funnel(fn0);
    free_funnel(fn1);
    //print_shortest_path(p, s0, 0);
    //print_shortest_path(p, s1, 1);
}

void bi_shortest_path_from_all(polytope *p) {
    int i;
    for (i = 0; i < p->N; i ++) {
        edge *e = p->vertices[i]->head;
        vertex *v0 = e->from, *v1 = e->to;
        bi_shortest_path_from(p, v0, v1);
    }
    printf(" - visibility computed - %dms\n", clock() - START_TIME);
    START_TIME = clock();
}

int to_visit(facet *f, vertex *v0, vertex *v1) {
    edge *e0 = f->loop, *e1 = e0->next, *e2 = e1->next;
    if (e2->next != e0) {
        return 0;
    }
    assert(e2->next == e0);
    vertex *m0 = new_vertex(
        (e0->from->x + e0->to->x) / 2, 
        (e0->from->y + e0->to->y) / 2, 0);
    if (check_segments_intersect(e0->next->to, m0, v0, v1)) {
        free_vertex(m0);
        return 1;
    }
    free_vertex(m0);
    vertex *m1 = new_vertex(
        (e1->from->x + e1->to->x) / 2, 
        (e1->from->y + e1->to->y) / 2, 0);
    if (check_segments_intersect(e1->next->to, m1, v0, v1)) {
        free_vertex(m1);
        return 1;
    }
    free_vertex(m1);
    vertex *m2 = new_vertex(
        (e2->from->x + e2->to->x) / 2, 
        (e2->from->y + e2->to->y) / 2, 0);
    if (check_segments_intersect(e2->next->to, m2, v0, v1)) {
        free_vertex(m2);
        return 1;
    }
    free_vertex(m2);
    return 0;
}

void split_edge_at(edge **e, vertex *v) {
    // need a better approach to detect\
    if the edge to split changes
    if (! check_on_segment(v, (*e)->from, (*e)->to)) {
        *e = (*e)->next;
        //assert(check_on_segment(v, (*e)->from, (*e)->to));
    }
    edge *e1 = *e;
    edge *e0 = (*e)->twin;
    edge *e1_0 = new_edge();
    edge *e0_0 = new_edge();

    e1_0->left_hand = e1->left_hand;
    e0_0->left_hand = e0->left_hand;

    e1_0->from = v;
    e1_0->to = e1->to;
    e0_0->from = v;
    e0_0->to = e0->to;
    e1->to = v;
    e0->to = v;

    e1_0->next = e1->next;
    e1->next->prev = e1_0;
    e1->next = e1_0;
    e1_0->prev = e1;

    e0_0->next = e0->next;
    e0->next->prev = e0_0;
    e0_0->prev = e0;
    e0->next = e0_0;

    e1->twin = e0_0;
    e0_0->twin = e1;
    e0->twin = e1_0;
    e1_0->twin = e0;

    v->head = e0_0;
}

edge *match_edge(vertex *v0, vertex *v1) {
    assert(v0 != NULL);
    assert(v0->head != NULL);
    edge *e = v0->head;
    do {
        if (e->to == v1) 
            return e;
        e = e->prev->twin;
    } while (e != v0->head);
    return NULL;
}

series *link_path_from(polytope *p, vertex *s0, vertex *s1) {
    int VISITED_COUNT = 0;
    int TIME_DFS = 0;
    int TIME_BFS = 0;
    int TIME_RETRI = 0;

    window **queue = (window **) get_buffer();
    facet **stack = (facet **) get_buffer();
    facet **queue_0 = (facet **) get_buffer();
    edge **stack_0 = (edge **) get_buffer();
    
    int head = 0, tail = 0, last_tail, top = 0;
    cache_window(p, s0, s1, NULL, NULL, queue, & tail, 0);
    queue[0]->depth = 0;
    queue[0]->parent = NULL;
    last_win = NULL;
    while (head < tail) {
        window *win = queue[head ++];
        // bi-dfs to compute the visibie sub-polygon \
        (and store the windows in the queue)
        TIME_DFS -= clock();
        set_source(win->v0, 0);
        set_source(win->v1, 1);
        edge *e = match_edge(win->v0, win->v1);
        assert(e != NULL);
        assert(e->from == win->v0 && e->to == win->v1);
        link_to_parent(win->v0,  win->v1, 0);
        funnel *fn0 = new_funnel(win->v0);
        fn0->right_chain = new_chain_node(win->v1);
        link_to_parent(win->v1, win->v0, 1);
        funnel *fn1 = new_funnel(win->v1);
        fn1->left_chain = new_chain_node(win->v0);
        last_tail = tail;
        if (e->left_hand != p->external)
            if (bi_depth_first_traverse(
                p, e, fn0, fn1, queue, & tail))
            {
                if (last_win->parent == NULL) {
                    vertex *v = lines_intersect(
                        last_win->v0, last_win->v1, 
                        win->v0, win->v1);
                    if (v == NULL) 
                    {
                        last_win->parent = win->parent;
                        last_win->depth = win->depth;
                    }
                    else {
                        last_win->parent = win;
                        last_win->depth = win->depth + 1;
                        free_vertex(v);
                    }
                }
            }
        free_funnel(fn0);
        free_funnel(fn1);
        TIME_DFS += clock();
        //bfs for facets corresponding to the windows
        TIME_BFS -= clock();
        int i, head_0 = 0, tail_0 = 0;
        for (i = last_tail; i < tail; i ++) {
            window *w = queue[i];
            w->parent = win;
            w->depth = win->depth + 1;
            int last_tail_0 = tail_0;
            edge *e0, *e;
            if (w->e0 == NULL)
                e = e0 = w->v0->head;
            else if (w->e1 == NULL)
                e = e0 = w->v1->head;
            else assert(0);
            do {
                if (e->left_hand != p->external &&
                    to_visit(e->left_hand, w->v0, w->v1)) 
                        break;
                e = e->prev->twin;
            } while (e != e0);
            if (to_visit(e->left_hand, w->v0, w->v1)) {
                queue_0[tail_0 ++] = e->left_hand;
                e->left_hand->visited = 1;
            }
            while (head_0 != tail_0) {
                facet *f = queue_0[head_0 ++];
                edge *e = f->loop;
                do {
                    assert(e->left_hand == f);
                    facet *f0 = e->twin->left_hand;
                    if (f0 != p->external && 
                        f0->visited == 0 && 
                        to_visit(f0, w->v0, w->v1)) 
                    {
                        queue_0[tail_0 ++] = f0;
                        f0->visited = 1;
                    }
                    e = e->next;
                } while (e != f->loop);
            }
            int j;
            for (j = last_tail_0; j < tail_0; j ++) 
                queue_0[j]->visited = 0;
        }
        for (i = 0; i < tail_0; i ++) 
            queue_0[i]->visited = 1;
        // remove duplicates
        VISITED_COUNT += tail_0;
        sort_by_address(queue_0, 0, tail_0 - 1);
        int top_0 = 0;
        for (i = 0; i < tail_0; i ++) {
            if (i == 0 || queue_0[i] != queue_0[i - 1]) {
                facet *f = queue_0[i];
                edge *e = f->loop;
                do {
                    if (e->to_delete == 0 && 
                        e->twin->left_hand->visited == 1) 
                    {
                        e->to_delete = 1;
                        e->twin->to_delete = 1;
                        stack_0[top_0 ++] = e;
                    }
                    e = e->next;
                } while (e != f->loop);
            }
        }
        // disconnect edges corresponding to the windows \
        (new larger facets are created to replace original ones)
        while (top_0 > 0) 
            disconnect_vertices(stack_0[-- top_0]);
        for (i = 0; i < tail_0; i ++) 
            queue_0[i]->visited = 0;
        // split edges on the boundary cut by the windows
        for (i = last_tail; i < tail; i ++) {
            window *w = queue[i];
            if (w->to_split == 0) 
                continue;
            if (w->e0 != NULL) {
                assert(w->e0->left_hand == p->external);
                split_edge_at(& (w->e0), w->v0);
            }
            else if (w->e1 != NULL) {
                assert(w->e1->left_hand == p->external);
                split_edge_at(& (w->e1), w->v1);
            }
            else assert(0);
        }
        // re-triangulate new facets
        for (i = last_tail; i < tail; i ++) {
            window *w = queue[i];
            edge *e0 = match_edge(w->v0, w->v1);
            if (e0 == NULL) {
                edge *e;
                if (w->e0 != NULL) {
                    e = connect_vertices_3(w->v0, w->v1, 
                        w->e0->twin->left_hand, 
                        w->e0->twin, NULL);
                }
                else if (w->e1 != NULL) {
                    e = connect_vertices_3(w->v0, w->v1, 
                        w->e1->twin->left_hand, 
                        NULL, w->e1->twin);
                }
                else assert(0);
                assert(e->next->next != e);
                TIME_BFS += clock();
                TIME_RETRI -= clock();
                if (MONOTONE_ONLY)
                    triangulate_monotone(e->left_hand);
                else 
                    triangulate_facet(e->left_hand);
                TIME_RETRI += clock();
                TIME_BFS -= clock();
                e->twin->left_hand->visited = 1;
                stack[top ++] = e->twin->left_hand;
            }
        }
        TIME_BFS += clock();
    }
    if (SHOW_DETAIL) {
        printf("     - %d vertex searches and %d facet searches\n", 
            VERTEX_SEARCH_COUNT, FACET_SEARCH_COUNT);
        printf("     - %d facets visited\n", VISITED_COUNT);
    }
    if (SHOW_DETAIL) {
        printf("     - %d windows allocated\n", tail - 1);
        printf("     - %dms for DFS, %dms for BFS and %dms for re-triangulation\n", 
            TIME_DFS, TIME_BFS, TIME_RETRI);
    }

    // obtain a result polyline through backtracking
    int i = last_win->depth + 1;
    series *result = new_series(i);
    window *prev_win = NULL, *cur_win = last_win;
    while (cur_win != NULL) {
        // the polyline vertex of the current depth is\
        the intersection of the current window and the previous window
        vertex *res;
        if (prev_win == NULL) {
            // intersection of the line <cur_win->v0, cur_win->v1>\
            and the edge DESTINATION
            res = lines_intersect(
                cur_win->v0, cur_win->v1, 
                DESTINATION->from, DESTINATION->to);
        }
        else {
            // intersection of the line <cur_win->v0, cur_win->v1>\
            and the line <prev_win->v0, prev_win->v1>
            res = lines_intersect(
                cur_win->v0, cur_win->v1, 
                prev_win->v0, prev_win->v1);
        }
        -- i;
        result->list[i][0] = res->x;
        result->list[i][1] = res->y;
        free_vertex(res);
        prev_win = cur_win;
        cur_win = cur_win->parent;
    }
    free_window(last_win);
    assert(i == 0);

    printf("     - links = %d\n", result->N);
    printf("     - compression ratio = %lf\n", 
        (double) p->series_len / result->N);
    for (head = 0; head < tail; head ++) {
        assert(queue[head] != NULL);
        free_window(queue[head]);
    }
    while (top > 0) 
        stack[-- top]->visited = 0;
    
    return_buffer((void **) queue);
    return_buffer((void **) stack);
    return_buffer((void **) queue_0);
    return_buffer((void **) stack_0);
    return result;
}

polytope *gen_tube_polygon(
    series *s, double tau, double eta) 
{
    polytope *p;
    p = gen_tube(s, tau, eta);
    p->series_len = s->N;
    return p;
}

series *link_path(series *input, double tau, double eta) {
    polytope *p;
    p = gen_tube_polygon(input, tau, eta);
    /*
    assert(sprint_check_simple_polygon(string_buffer, p));
    printf("checked - %dms\n", clock() - START_TIME);
    START_TIME = clock();
    */
    SOURCE = p->vertices[0]->head;
    DESTINATION = NULL;
    int i; 
    for (i = 0; i < p->N; i ++) {
        if (DESTINATION == NULL ||
            dist2(SOURCE->from, p->vertices[i]) > 
            dist2(SOURCE->from, DESTINATION->from)) 
        {
            DESTINATION = p->vertices[i]->head;
        }
    }
    if (SHOW_DETAIL) {
        printf("     - source: ");
        print_edge(SOURCE);
        printf("\n");
        printf("     - destination: ");
        print_edge(DESTINATION);
        printf("\n");
        printf("     - polygon size = %d\n", p->N);
    }
    printf("   - polygon generated - %dms\n", clock() - START_TIME);
    START_TIME = clock();
    triangulate_polygon(p);
    series *output;
    output = link_path_from(p, SOURCE->from, SOURCE->to);
    check_result(input, output, tau, eta);
    printf("   - link distance computed - %dms\n", clock() - START_TIME);
    START_TIME = clock();
    free_polytope(p);
    return output;
}

void init() {
    VERTEX_SEARCH_COUNT = 0;
    FACET_SEARCH_COUNT = 0;
    START_TIME = clock();
    srand(time(0));
    new_pointer_buffers();
    new_bst();
    funnel_count[0] = chain_node_count[0] = 0;
    funnel_count[1] = chain_node_count[1] = 0;
    window_count = 0;
    printf(" - initialization done - %dms\n", clock() - START_TIME);
    START_TIME = clock();
}

void clear() {
    if (SHOW_DETAIL) {
        printf("   - %d funnels and %d chain nodes allocated\n", 
            funnel_count[1], chain_node_count[1]);
    }
    assert(window_count == 0);
    assert(funnel_count[0] == 0);
    assert(chain_node_count[0] == 0);
    free_bst();
    free_pointer_buffers();
    printf(" - clear done - %dms\n", clock() - START_TIME);
}

int main() {
    printf(" - start\n");
    init();
    double tau = 10, eta = 0.333333;
    printf(" - error bounds set: tau = %lf, eta = %lf\n", tau, eta);
    series *s = gen_series(10000, 30, 1);
    //series *s = new_series_from("input.txt");
    free_series(greedy_link_path(s, tau, eta));
    free_series(DP_link_path(s, tau, eta));
    printf(" - baselines done\n");
    free_series(link_path(s, tau, eta));
    printf(" - temporal compression done\n");
    free_series(s);
    clear();
    return EXIT_SUCCESS;
}
