/*
This program contains data pre-processing, 
data decomposition and spatial data compression.
It also generates temporal sequences 
for the following temporal compression, 
which should be done by temporal compression algorithms
in the other program.

The code has not been re-written but it works. : )

This program should only be shared within the MDM group.
Do NOT make it public without the permission of Prof. Sun.

If you have any other problems, contact me via
yunhenghan19 at gmail dot com.
*/

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <math.h>
#include <windows.h>
#include <time.h>
#define maxN 100000
#define maxM 210000
#define maxK 2000000
#define maxT 2000000
#define EARTH_RADIUS 6371009
#define PI 3.14159265359
#define DEG 180
#define BASE 0xFFFFF
#define maxH 100000
#define SHORT_INF 65535
#define maxC 132206
#define maxD 80000000
#define maxDEG 10
#define RAD 0.01745329252
#define dist_eps 0.1

typedef struct coord_l {
	double lat, lon;
} coord_l;

typedef struct coord_c {
	double x, y, z;
} coord_c;

typedef struct bst_node {
	struct bst_node *l, *r;
	int key, h, s;
	struct trie_node *data;
} bst_node;

typedef struct trie_node {
	struct bst_node *next;
	struct trie_node *prev;
	int code, ch, depth;
} trie_node;

typedef struct queue_node {
	double key;
	int data;
	struct queue_node *child, *next, *prev;
} queue_node;

typedef struct hash_node {
	int from, to, count;
	struct hash_node *next;
} hash_node;

typedef struct joints {
	struct coord_l joint;
	struct joints *next;
} joints;

typedef struct edge {
	double dist;
	int id, from, to, label, count;
	struct joints *head;
	struct edge *next;
} edge;

typedef struct node {
	double lat, lon;
	int id, in, out;
} node;

typedef struct sample_point {
	coord_l sample;
	int time, edge;
} sample_point;

typedef struct temporal_point {
	double dist;
	int time;
} temporal_point;

node nodes[maxN];
edge *edges[maxM], *adj_list[maxN];
queue_node *queue_null, **buffer, **refer;
int N, M;
hash_node hash_pool[maxH], *hash_list[BASE];
unsigned short **table;
bst_node *null;
int stack[maxK], top;
sample_point input_point[maxT]; temporal_point output_point[maxT]; int T;
int K, input[maxK], sinput[maxK], Krs, soutput[maxK], Ks, foutput[maxK], Kf, sfoutput[maxK], Ksf, recover[maxK], Kr;
int trie_count, bst_count, step_count, queue_count, hash_count;
int ALPHABET_SIZE, DICT_SIZE, STEP, DECODE_TEST;
trie_node *dict_root, *sdict_root;
int tK, tKs, tKf, tKsf;

int sgn(double t) {
	if (fabs(t) < dist_eps) return 0;
	if (t < 0) return -1;
	return +1;
}

coord_l new_coord_l(double lat0, double lon0) {
	coord_l t;
	t.lat = lat0 * RAD;
	t.lon = lon0 * RAD;
	return t;
}

coord_c l2c(coord_l A) {
	coord_c t;
	t.x = cos(A.lat) * cos(A.lon);
	t.y = cos(A.lat) * sin(A.lon);
	t.z = sin(A.lat);
	return t;
}

coord_l c2l(coord_c A) {
	coord_l t;
	t.lat = asin(A.z);
	t.lon = atan2(A.y, A.x);
	return t;
}

coord_c vector_product(coord_c A, coord_c B) {
	coord_c t;
	t.x = A.y * B.z - A.z * B.y;
	t.y = A.z * B.x - A.x * B.z;
	t.z = A.x * B.y - A.y * B.x;
	return t;
}

double dot(coord_c A, coord_c B) {
	return A.x * B.x + A.y * B.y + A.z * B.z;
}

coord_c multiply(coord_c A, double scalar) {
	coord_c t;
	t.x = A.x * scalar;
	t.y = A.y * scalar;
	t.z = A.z * scalar;
	return t;
}

void print_l(coord_l A) {
    printf("%f %f\n", A.lat / RAD, A.lon / RAD);
}

void print_c(coord_c A) {
    printf("%f %f %f %f\n", A.x, A.y, A.z, sqrt(dot(A, A)));
}

double dist(coord_l A, coord_l B) {
	//spherical law of cosines
	double t = sin(A.lat) * sin(B.lat) + cos(A.lat) * cos(B.lat) * cos(A.lon - B.lon);
	if (t > 1) return 0;
	return EARTH_RADIUS * sqrt(2 - 2 * t);
}

/*
distance from a point to a line segment on a sphere
http://stackoverflow.com/questions/1299567
*/
coord_l nearest_point_circle(coord_l A, coord_l B, coord_l C) {
	coord_c tA = l2c(A), tB = l2c(B), tC = l2c(C);
	coord_c G = vector_product(tA, tB);
	coord_c F = vector_product(tC, G);
	coord_c t = vector_product(G, F);
	t = multiply(t, 1 / sqrt(dot(t, t)));
	return c2l(t);
}

coord_l nearest_point_segment(coord_l A, coord_l B, coord_l C) {
	coord_l t = nearest_point_circle(A, B, C);
	if (on_segment(A, B, t)) return t;
	return (dist(A, C) < dist(B, C)) ? A : B;
}

int on_segment(coord_l A, coord_l B, coord_l C) {
	double t = dist(A, C) + dist(B, C) - dist(A, B);
	//printf("%f\n", t);
	return sgn(t) == 0;
}

queue_node *new_queue(double key, int data) {
	queue_node *temp = (queue_node *)malloc(sizeof(queue_node)); queue_count ++;
	temp->key = key;
	temp->data = data;
	temp->child = temp->next = temp->prev = queue_null;
	return temp;
}

queue_node *queue_link(queue_node *a, queue_node *b) {
	if (a == queue_null) return b;
	if (b == queue_null) return a;
	if (a->key > b->key) {
		queue_node *temp = a;
		a = b; b = temp;
	}
	b->next = a->child;
	if (a->child != queue_null)
		a->child->prev = b;
	a->child = b;
	b->prev = a;
	return a;
}

queue_node *queue_extract(queue_node *root) {
	queue_node *a = root->child;
	free(root); queue_count --;
	root = NULL;
	if (a == queue_null) return queue_null;
	a->prev = queue_null;
	int k = 0, i;
	queue_node *b, *c, *res;
	while (a != queue_null) {
		b = a->next; c = b->next;
		a->next = queue_null; b->prev = queue_null;
		b->next = queue_null; c->prev = queue_null;
		buffer[++ k] = queue_link(a, b);
		a = c;
	}
	root = buffer[k]; i = k - 1;
	while (i > 0) {
		root = queue_link(root, buffer[i]);
		i --;
	}
	return root;
}

queue_node *queue_insert(queue_node *root, queue_node *temp) {
	return queue_link(root, temp);
}

queue_node *queue_decrease(queue_node *root, queue_node *b, double key) {
	queue_node *a = b->prev, *c = b->next;
	b->key = key;
	if (b == root) return root;
	if (a->child == b)
		a->child = c;
	else
		a->next = c;
	if (c != queue_null) c->prev = a;
	b->prev = queue_null; b->next = queue_null;
	return queue_link(root, b);
}

void delete_queue(queue_node *root) {
	if (root == queue_null) return ;
	queue_node *p = root->child;
	while (p != queue_null) {
		delete_queue(p);
		p = p->next;
	}
	free(root); queue_count --;
	root = NULL;
}

void init_queue() {
	buffer = (queue_node **)malloc(sizeof(queue_node *) * maxN);
	refer = (queue_node **)malloc(sizeof(queue_node *) * maxN);
	queue_null = (queue_node *)malloc(sizeof(queue_node));
	queue_null->prev = queue_null->next = queue_null->child = queue_null;
	queue_count = 0;
}

void test_queue(int N) {
	srand(time(NULL));
	queue_node *root = queue_null;
	int i;
	for (i = 0; i < N; i ++) {
		int j = rand();
		queue_node *temp = new_queue((double) j, j);
		root = queue_insert(root, temp);
		//printf("%d ", j);
	}
	printf("(%d)\n", N);
	int last = 0;
	for (i = 0; root != queue_null; i ++) {
		//printf("%d ", root->data);
		assert(root->data >= last);
		last = root->data;
		root = queue_extract(root);
	}
	printf("(%d)\n", i);
	delete_queue(root);
}

bst_node *new_bst(int key, trie_node *data) {
	bst_node *temp = (bst_node *)malloc(sizeof(bst_node));
	bst_count ++;
	temp->key = key;
	temp->data = data;
	temp->l = temp->r = NULL;
	return temp;
}

void update(bst_node *x) {
	if (x->l->h > x->r->h)
		x->h = x->l->h + 1;
	else
		x->h = x->r->h + 1;
	x->s = x->l->s + x->r->s + 1;
}

bst_node *rotr(bst_node *x) {
	bst_node *y = x->l;
	x->l = y->r;
	y->r = x;
	update(x); update(y);
	return y;
}

bst_node *rotl(bst_node *x) {
	bst_node *y = x->r;
	x->r = y->l;
	y->l = x;
	update(x); update(y);
	return y;
}

bst_node *balance(bst_node *x) {
	if (x->l->h > x->r->h + 1) {
		if (x->l->r->h > x->l->l->h)
			x->l = rotl(x->l);
		x = rotr(x);
	}
	if (x->r->h > x->l->h + 1) {
		if (x->r->l->h > x->r->r->h)
			x->r = rotr(x->r);
		x = rotl(x);
	}
	return x;
}

bst_node *insert(bst_node *x, int key, trie_node *data) {
	if (x == null) {
		bst_node *temp = new_bst(key, data);
		temp->l = temp->r = null;
		temp->h = 0;
		return temp;
	}
	else {
		if (key <= x->key)
			x->l = insert(x->l, key, data);
		else
			x->r = insert(x->r, key, data);
		update(x);
		x = balance(x);
		return x;
	}
}

bst_node *del_max(bst_node *x, bst_node **temp) {
	if (x->r == null) {
		*temp = x;
		return x->l;
	}
	x->r = del_max(x->r, temp);
	update(x);
	x = balance(x);
	return x;
}

bst_node *delete(bst_node *x, int key) {
	if (key < x->key) x->l = delete(x->l, key);
	if (key > x->key) x->r = delete(x->r, key);
	if (key == x->key) {
		bst_node *y = NULL;
		if (x->l == null) y = x->r;
		if (x->r == null) y = x->l;
		if (y != NULL) {
			free(x); bst_count --;
			return y;
		}
		x->l = del_max(x->l, &y);
		x->key = y->key;
		x->data = y->data;
		free(y); bst_count --;
	}
	update(x);
	x = balance(x);
	return x;
}

bst_node *search(bst_node *x, int key) {
	if (x == null) return null;
	if (key == x->key) return x;
	if (key < x->key)
		return search(x->l, key);
	else
		return search(x->r, key);
}

trie_node *new_trie(int code, int ch, int depth) {
	trie_node *temp = (trie_node *)malloc(sizeof(trie_node));
	trie_count ++;
	temp->code = code;
	temp->ch = ch;
	temp->depth = depth;
	temp->next = null;
	temp->prev = NULL;
	return temp;
}

void delete_trie(trie_node *root);

void delete_bst(bst_node *root) {
	if (root == null) return ;
	delete_bst(root->l);
	delete_trie(root->data);
	delete_bst(root->r);
	free(root);
	bst_count --;
}

void delete_trie(trie_node *root) {
	delete_bst(root->next);
	free(root);
	trie_count --;
}

void delete_dict(trie_node *root) {
	//printf("%d %d\n", bst_count, trie_count);
	free((trie_node **)root->prev);
	delete_trie(root);
}

void trie_link(trie_node *a, trie_node *b) {
	b->prev = a;
	a->next = insert(a->next, b->ch, b);
}

trie_node *load_dict(char *file_name) {
	FILE *fin = fopen(file_name, "r");
	if (fin == NULL) return NULL;
	trie_node *root = new_trie(0, -1, -1);
	fscanf(fin, "%d", &root->code);
	trie_node **index = (trie_node **)malloc(sizeof(trie_node *) * (N + root->code));
	root->prev = (void *)index;
	int i;
	for (i = 0; i < root->code; i ++) {
		int ch, pcode;
		fscanf(fin, "%d%d", &ch, &pcode);
		trie_node *prev = root;
		if (pcode != -1) prev = index[pcode];
		trie_node *temp = new_trie(i, ch, prev->depth + 1);
		trie_link(prev, temp);
		index[i] = temp;
	}
	fclose(fin);
	return root;
}

void store_dict(trie_node *root, char *file_name) {
	FILE *fout = fopen(file_name, "w");
	trie_node **index = (trie_node **)root->prev;
	fprintf(fout, "%d\n", root->code);
	int i;
	for (i = 0; i < root->code; i ++) {
		int pcode = -1;
		if (index[i]->prev != root) pcode = index[i]->prev->code;
		fprintf(fout, "%d %d\n", index[i]->ch, pcode);
	}
	fclose(fout);
}

void restore_dict(trie_node *root, int size) {
	trie_node **index = (trie_node **)root->prev;
	while (root->code > size) {
		trie_node *cur = index[-- root->code];
		cur->prev->next = delete(cur->prev->next, cur->ch);
		free(cur); trie_count --;
	}
}

trie_node *init_trie() {
	trie_node *root = new_trie(0, -1, -1); // root->code stores the size of the trie
	trie_node **index = (trie_node **)malloc(sizeof(trie_node *) * DICT_SIZE);
    root->prev = (void *)index; // root->prev stores the index (code ~> trie_node)
	int i;
	for (i = 0; i < ALPHABET_SIZE; i ++) {
		trie_node *temp = new_trie(i, i, 0);
		index[i] = temp;
		trie_link(root, temp);
		root->code ++;
	}
	return root;
}

int n2b(int n) {
	int i;
	for (i = 0, n = n - 1; n > 0; n >>= 1, i ++);
	return i;
}

int write_bits(int *buffer, int count, int code, int bits) {
	int s = sizeof(int) * 8;
	int a = count / s, b = s - 1 - count % s;
	int i;
	for (i = bits - 1; i >= 0; i --) {
		int j = code & (1 << i);
		if (j != 0)
			buffer[a] = buffer[a] | (1 << b);
		if (-- b < 0) {
			b = s - 1;
			a ++;
		}
		count ++;
	}
	return count;
}

int read_bits(int *buffer, int count, int *code, int bits) {
    int s = sizeof(int) * 8;
	int a = count / s, b = s - 1 - count % s;
	*code = 0;
	int i;
	for (i = bits - 1; i >= 0; i --) {
		int j = buffer[a] & (1 << b);
		if (j != 0)
			*code = *code | (1 << i);
		if (-- b < 0) {
			b = s - 1;
			a ++;
		}
		count ++;
	}
	return count;
}

int flag = 0;

int encode(trie_node *root, int *input, int N, int *output) {
	int M = 0;
	/*
	if (dict_root->code > step_count) {
		step_count += STEP;
		flag = 1;
	}
	*/
	if (flag == 1) printf("dict refs (%d) MB (%d)\n", root->code, root->code * (n2b(root->code) + n2b(ALPHABET_SIZE)) / (1024 * 1024 * 8));
	int size = root->code;
	trie_node **index = (trie_node **)root->prev;
	trie_node *cur = root;
	int i;
	for (i = 0; i < N; i ++) {
		trie_node *next = search(cur->next, input[i])->data;
		if (next != NULL)
			cur = next;
		else {
			M = write_bits(output, M, cur->code, n2b(root->code));
			next = new_trie(root->code, input[i], cur->depth + 1);
			index[root->code ++] = next;
			trie_link(cur, next);
			cur = root; i --;
		}
	}
	if (i == N) {
		M = write_bits(output, M, cur->code, n2b(root->code));
	}
	if (DECODE_TEST == 1) restore_dict(root, size);
	return M;
}

int decode(trie_node *root, int *output, int M, int *input) {
	int N = 0;
	if (flag == 1) printf("dict refs (%d) MB (%d)\n", root->code, root->code * (n2b(root->code) + n2b(ALPHABET_SIZE)) / (1024 * 1024 * 8));
	trie_node **index = (trie_node **)root->prev;
	trie_node *cur, *last = NULL;
	int i = 0, temp;
	while (i < M) {
		int code = 0;
		i = read_bits(output, i, &code, n2b(root->code + (i != 0)));
        if (code <= root->code - 1) {
			cur = index[code];
			trie_node *p;
			for (p = cur; p != root; p = p->prev)
				input[N + p->depth] = p->ch;
			temp = input[N]; // the char to be inserted after last
			N += cur->depth + 1;
			if (last != NULL) {
				trie_node *next = new_trie(root->code, temp, last->depth + 1);
				index[root->code ++] = next;
				trie_link(last, next);
			}
			last = cur;
        }
        else {
			trie_node *p;
			for (p = last; p != root; p = p->prev)
				input[N + p->depth] = p->ch;
			N += last->depth + 1;
			input[N ++] = temp;
			trie_node *next = new_trie(root->code, temp, last->depth + 1);
			index[root->code ++] = next;
			trie_link(last, next);
			last = next;
		}
	}
	return N;
}

void print_array(int *buffer, int N, int full) {
	if (full == 1) {
		int i;
		for (i = 0; i < N; i ++)
			printf("%d ", buffer[i]);
	}
	printf("input bits (%d)\n", N * n2b(ALPHABET_SIZE));
}

int cmp(int *a, int A, int *b, int B) {
	if (A != B) return 1;
	int i;
	for (i = 0; i < A; i ++)
        if (a[i] != b[i]) return 1;
	return 0;
}

void print_res() {
	int i;
	for (i = 0; foutput[i] != 0; i ++)
		foutput[i] = 0;
	for (i = 0; sfoutput[i] != 0; i ++)
		sfoutput[i] = 0;
	tK += K;
	tKs += Ks;
	tKf += Kf;
	tKsf += Ksf;
	if (flag == 1) {
		printf("compression ratio (%f %f %f)\n", (double) tK / tKs, (double) tK * n2b(ALPHABET_SIZE) / tKf, (double) tK * n2b(ALPHABET_SIZE) / tKsf);
		tK = tKs = tKf = tKsf = 0;
	}
	flag = 0;
}

void frequent_path_encode() {
	Kf = encode(dict_root, input, K, foutput);
    if (DECODE_TEST == 1) Kr = decode(dict_root, foutput, Kf, recover);
    if (DECODE_TEST == 1) assert(cmp(input, K, recover, Kr) == 0);
	/*
	Ksf = encode(sdict_root, soutput, Ks, sfoutput);
    if (DECODE_TEST == 1) Kr = decode(sdict_root, sfoutput, Ksf, recover);
    if (DECODE_TEST == 1) assert(cmp(soutput, Ks, recover, Kr) == 0);
	*/
	print_res();
}

void print_graph_para() {
	printf("%d nodes, %d edges\n", N, M);
	int i, j; double avg;
	for (i = 0, j = 0, avg = 0; i < M; i ++) {
		joints *p, *q; double dist0;
		for (dist0 = 0, p = edges[i]->head, q = NULL; p != NULL; q = p, p = p->next, j ++) {
			if (q != NULL)
				dist0 += dist(p->joint, q->joint);
		}
		avg += dist0 / M;
	}
	printf("average edge length %f\n", avg);
	printf("average edge joints# %f\n", (double) j / M);
}

void init_adj_list(char *node_name, char *edge_name) {
	FILE* fin = fopen(node_name, "r");
	for (N = 0; fscanf(fin, "%d %lf %lf", &nodes[N].id, &nodes[N].lat, &nodes[N].lon) != EOF; N ++) {
		nodes[N].lat *= RAD;
		nodes[N].lon *= RAD;
		nodes[N].in = nodes[N].out = 0;
		adj_list[N] = NULL;
	}
	fclose(fin);
	fin = fopen(edge_name, "r");
	int id, from, to, len;
	for (M = 0; fscanf(fin, "%d %d %d", &id, &from, &to) != EOF; M ++) {
		edge *temp = (edge *) malloc(sizeof(edge));
		edges[M] = temp;
		temp->id = id;
		temp->from = from;
		temp->to = to;
		temp->count = 0;
		temp->label = -1;
		fscanf(fin, "%d", &len);
		int i; joints *p, *q; double dist0;
		for (i = 0, temp->head = p = NULL, dist0 = 0; i < len; i ++, p = q) {
			q = (joints *)malloc(sizeof(joints));
			fscanf(fin, "%lf %lf", &q->joint.lat, &q->joint.lon);
			q->joint.lat *= RAD;
			q->joint.lon *= RAD;
			q->next = NULL;
			if (p == NULL)
				temp->head = q;
			else {
				p->next = q;
				dist0 += dist(p->joint, q->joint);
			}
		}
		temp->dist = dist0;
		temp->next = adj_list[from];
		adj_list[from] = temp;
		nodes[from].out ++;
		nodes[to].in ++;
	}
	fclose(fin);
	//print_graph_para();
}

unsigned short prev[maxN];
int depth[maxN];
double distance[maxN];

int dijkstra(int source) {
	queue_node *root = queue_null;
	int i, j = 0;
	for (i = 0; i < N; i ++) {
		refer[i] = NULL;
		prev[i] = SHORT_INF;
		depth[i] = 0;
		distance[i] = -1;
	}
	queue_node *temp = new_queue(0, source);
	root = queue_insert(root, temp);
	refer[source] = temp;
	for (i = 0; root != queue_null; i ++) {
		int from = root->data;
		double dist0 = root->key;
		refer[from] = NULL;
		root = queue_extract(root);
		edge *p;
		for (p = adj_list[from]; p != NULL; p = p->next) {
			int to = p->to;
			double dist1 = dist0 + p->dist;
			if (distance[to] < 0 || dist1 < distance[to]) {
				distance[to] = dist1;
				prev[to] = (unsigned short) from;
				depth[to] = depth[from] + 1;
				if (refer[to] != NULL)
					root = queue_decrease(root, refer[to], dist1);
				else {
					queue_node *temp = new_queue(dist1, to);
					root = queue_insert(root, temp);
					refer[to] = temp;
				}
			}
		}
	}
	assert(queue_count == 0);
	return i;
}

int shortest_path(int s, int d) {
	if (table[s][d] == SHORT_INF) return 1;
	int i;
	for (i = d; i != s; i = table[s][i])
		printf("%d ", i);
	printf("%d\n", s);
	return 0;
}

void dijkstra_build_table(const char* table_name) {
	printf("building prev table ...");
	int i, j;
	FILE *fout = fopen(table_name, "wb");
	for (i = 0, j = 0; i < 600; i ++) {
		dijkstra(i);
		fwrite(prev, sizeof(unsigned short), N, fout);
		if (i % 600 == 0) printf(" %d\n", j ++);
		if (i % 60 == 0) printf(".");
	}
	fclose(fout);
	printf("table stored\n");
}

void load_table(const char* table_name) {
	printf("loading prev table ...");
	FILE *fin = fopen(table_name, "rb");
	int i;
	table = (unsigned short **)malloc(sizeof(unsigned short *) * N);
	for (i = 0; i < N; i ++) {
		table[i] = (unsigned short *)malloc(sizeof(unsigned short) * N);
		fread(table[i], sizeof(unsigned short), N, fin);
	}
	fclose(fin);
	printf("table loaded\n");
}

typedef int (*proc_file)(const char* name);

int scan_folder(const char* path, const char *filter, proc_file proc) {
	int len = strlen(path) + MAX_PATH;
	char *path_s = (char *)malloc(sizeof(char) * len);
    sprintf(path_s, "%s\\%s", path, filter);
	WIN32_FIND_DATA data;
	HANDLE find_h = FindFirstFile(path_s, &data);
	if (find_h == INVALID_HANDLE_VALUE) {
		free(path_s);
		return 1;
	}
	else do {
		if (data.cFileName[0] == '.')
			continue;
		sprintf(path_s, "%s\\%s", path, data.cFileName);
		printf("%s\n", path_s);
		int proc_t = proc(path_s);
	} while (FindNextFile(find_h, &data));
	FindClose(find_h);
	free(path_s);
	return 0;
}

int sample_proc(const char* name) {
	int len = 256;
	char *path_s = (char *)malloc(sizeof(char) * len);
	FILE *fin = fopen(name, "r");
	fscanf(fin, "%s", path_s);
	printf("%s\n", path_s);
	fclose(fin);
	return 0;
}

void init_hash() {
	int i;
	for (i = 0; i < BASE; i ++)
		hash_list[i] = NULL;
	hash_count = 0;
}

int hash_insert(int from, int to) {
	int key = (from * 131 + to * 13131) & BASE;
	hash_node *p = hash_list[key];
	while (p != NULL) {
		if (p->from == from && p->to == to) {
			p->count ++;
			return 1;
		}
        p = p->next;
	}
	hash_node *temp = hash_pool + hash_count ++;
	temp->from = from;
	temp->to = to;
	temp->count = 1;
	temp->next = hash_list[key];
	hash_list[key] = temp;
	return 0;
}

int check_consistency() {
	int i, j;
	edge *temp, *last = NULL;
	for (i = 0, j = K; i < K; i ++) {
		temp = edges[input[i]];
		if (last != NULL && last->to != temp->from)
			j --;
		last = temp;
	}
	return j;
}

int count_frequency() {
	int i;
	for (i = 0; i < K; i ++) {
		edge *temp = edges[input[i]];
		temp->count ++;
	}
	return 0;
}

int shortest_path_encode() {
	Ks = 0;
	int i, j, k;
	soutput[Ks ++] = input[0];
	for (i = 1, j = 0; i < K - 1; i ++) {
		int a = edges[input[j]]->to;
		int b = edges[input[i+1]]->from;
		int c = edges[input[i+1]]->to;
		if (table[a][c] != b) {
			soutput[Ks ++] = input[i];
			j = i;
		}
	}
	if (K > 1) soutput[Ks ++] = input[K - 1];
	Krs = 0;
	sinput[Krs ++] = soutput[0];
	for (i = 1; i < Ks; i ++) {
		int a = edges[soutput[i-1]]->to;
		int b = edges[soutput[i]]->from;
		if (a != b) {
			top = 0;
			for (j = b; j != a; j = k) {
				k = table[a][j];
				edge *temp;
				for (temp = adj_list[k]; temp != NULL; temp = temp->next)
					if (temp->to == j) break;
				stack[top ++] = temp->id;
			}
			while (top > 0) {
				sinput[Krs ++] = stack[-- top];
			}
		}
		sinput[Krs ++] = soutput[i];
	}
	return Ks;
}

int proc_edges_file(const char* name) {
	FILE *fin = fopen(name, "r");
	int data, i, check_sum = 0;
	for (fscanf(fin, "%d", &data), i = 0, K = 0; ; i ++, K = 0) {
		if (data > 0) input[K ++] = data;
		while (1) {
			if (fscanf(fin, "%d", &data) == EOF) { //EOF token
				//new input
				//shortest_path_encode();
				//frequent_path_encode();
				count_frequency();
				check_sum -= check_consistency();
				goto break_loop;
			}
			if (data < 0) break; //negative token
			check_sum ++;
			if (K > 0 && edges[input[K-1]]->to != edges[data]->from) break; //inconsistent token
			input[K ++] = data;
		}
		//new input
		//shortest_path_encode();
		//frequent_path_encode();
		count_frequency();
		check_sum -= check_consistency();
	}
	break_loop: // goto here to break
	assert(check_sum == 0);
	return 0;
}

void print_decomposition_para(int count, int tK, int tT) {
	printf("trajectory # %d\n", count);
	printf("sp edges total # %d, avg # %f\n", tK, (double)tK / count);
	printf("ts tuples total # %d, avg # %f\n", tT, (double)tT / count);
}

void decomposition(int count) {
	int i, j; double dist0;
	for (i = 0, j = 0, dist0 = 0; i < T; i ++) {
		while (j != input_point[i].edge) {
			dist0 += edges[input[j]]->dist;
			j ++;
		}
		edge *temp = edges[input[j]];
		joints *p, *q; double min_dist, bias, min_bias; coord_l min_t;
		for (min_dist = -1, p = temp->head, q = NULL, bias = 0; p != NULL; q = p, p = p->next) {
			if (q != NULL) {
				coord_l t = nearest_point_segment(p->joint, q->joint, input_point[i].sample);
				double dist1 = dist(t, input_point[i].sample);
				if (min_dist < 0 || dist1 < min_dist) {
					min_t = t;
					min_dist = dist1;
					min_bias = bias + dist(t, p->joint);
				}
				bias += dist(p->joint, q->joint);
			}
		}
		output_point[i].dist = dist0 + bias;
		output_point[i].time = input_point[i].time;
		assert(i == 0 || sgn(output_point[i].dist - output_point[i-1].dist) >= 0);
		assert(i == 0 || output_point[i].time > output_point[i-1].time);
	}
	/*
	char buffer[256];
	sprintf(buffer, "decomp_sp\\%08d.txt", count);
	FILE *fout = fopen(buffer, "w");
	for (i = 0; i < K; i ++)
		fprintf(fout, "%d ", input[i]);
	fclose(fout);
	sprintf(buffer, "decomp_ts\\%08d.txt", count);
	fout = fopen(buffer, "w");
	for (i = 0; i < T; i ++)
		fprintf(fout, "%f,%d ", output_point[i].dist, output_point[i].time);
	fclose(fout);
	*/
}

int average_speed(int count) {
	int i, ret; double s0, t0, v0;
	for (i = 1, ret = 0, s0 = 0, t0 = 0; i < T; i ++) {
		double s = dist(input_point[i].sample, input_point[i-1].sample);
		double t = input_point[i].time - input_point[i-1].time;
		double v = s / t;
		s0 += s;
		t0 += t;
		v0 = s0 / t0;
		if (v > 30) ret ++;
	}
	printf("%f\n", v0); system("pause");
	return ret;
}

int proc_mm_file(const char* name) {
	FILE *fin = fopen(name, "r");
	int data, i, j, k, count = 0, tK = 0, tT = 0, tR = 0;
	int time0 = 0;
	for (i = 0, T = K = 0; fscanf(fin, "%d", &data) != EOF ; i ++) { //EOF token
		if (data < 0) { //negative token
			//new input
			if (count % 1000 == 0) printf("%d ", count);
			if (count > 100000) goto break_loop2;
			//assert(check_consistency() == K);
			time0 -= clock();
			decomposition(count);
			time0 += clock();
			count ++; tK += K; tT += T;
			T = K = 0;
		}
		else {
			double lat, lon; int dummy, e, start, end;
			fscanf(fin, "%lf %lf %d %d", &lat, &lon, &dummy, &e);
			if (e == -1) continue;
			assert(dummy == -1);
			if (K == 0 || e != input[K-1]) { //new edge
				if (K > 0 && (start = edges[input[K-1]]->to) != (end = edges[e]->from)) { //inconsistent token
					if (table[start][end] == SHORT_INF) {
						//new input
						if (count % 1000 == 0) printf("%d ", count);
						if (count > 100000) goto break_loop2;
						//assert(check_consistency() == K);
						time0 -= clock();
						decomposition(count);
						time0 += clock();
						tK += K; tT += T; count ++;
						T = K = 0;
					}
					else {
						top = 0;
						for (j = end; j != start; j = k) {
							k = table[start][j];
							edge *temp;
							for (temp = adj_list[k]; temp != NULL; temp = temp->next)
								if (temp->to == j) break;
							stack[top ++] = temp->id;
						}
						while (top > 0) {
							input[K ++] = stack[-- top];
						}
					}
				}
				input[K ++] = e;
			}
			if (T == 0 || data > input_point[T-1].time) {
				input_point[T].time = data;
				input_point[T].sample.lat = lat * RAD;
				input_point[T].sample.lat = lon * RAD;
				input_point[T ++].edge = K - 1;
			}
		}
	}
	break_loop2:
	print_decomposition_para(count, tK, tT);
	printf("%dms\n", time0);
	return 0;
}

void sort(int l, int r) {
	int x = input[(l + r) / 2];
	int i = l, j = r;
	while (i <= j) {
        while (input[i] < x) i ++;
        while (input[j] > x) j --;
        if (i <= j) {
			int temp = input[i];
			input[i] = input[j];
			input[j] = temp;
			temp = sinput[i];
			sinput[i] = sinput[j];
			sinput[j] = temp;
			i ++; j --;
        }
	}
	if (i < r) sort(i, r);
	if (l < j) sort(l, j);
}

int lzw_compress(double prec) {
	int i, j;
	for (i = 0; i < T; i ++) {
		input[i] = (int) (input_point[i].sample.lat / prec);
		sinput[i] = i;
	}
	sort(0, T - 1);
	for (i = 0, j = 0; i < T; i ++) {
		if (i == 0 || input[i] != input[i-1])
			j ++;
		soutput[sinput[i]] = j;
	}
	printf("*%d*\n", j);
	Ks = T;
	Ksf = encode(sdict_root, soutput, Ks, sfoutput);
	return Ksf;
}

int entropy_compress(double prec) {
	int i, j;
	for (i = 0; i < T; i ++) {
		input[i] = (int) (input_point[i].sample.lat / prec);
		sinput[i] = i;
	}
	sort(0, T - 1);
	int k; double entropy;
	for (i = 0, j = 0, k = 0, entropy = 0; i <= T; i ++) {
		if (i == 0 || i == T || input[i] != input[i-1]) {
			double p = (double) k / T;
			printf("%f_", p);
			if (p != 0) entropy += - p * log2(p);
			k = 0; j ++;
		}
		k ++;
	}
	printf("%d %f\n", j, entropy);
	return (int) (T * entropy);
}

int direct_compress_mm_file(const char* name) {
	FILE *fin = fopen(name, "r");
	int data, i, j, k, count = 0, tT = 0, tK = 0, tK2 = 0;
	for (i = 0, T = 0; fscanf(fin, "%d", &data) != EOF ; i ++) { //EOF token
		if (data < 0) { //negative token
			//new input
		}
		else {
			double lat, lon; int dummy, e, start, end;
			fscanf(fin, "%lf %lf %d %d", &lat, &lon, &dummy, &e);
			if (e == -1) continue;
			assert(dummy == -1);
			input_point[T].time = data;
			input_point[T].sample.lat = lat;
			input_point[T].sample.lon = lon;
			//if (T == 0 || sgn(input_point[T].sample.lat - input_point[T-1].sample.lat) != 0)
			T ++;
			if (T > 20000) break;
		}
	}
	tT = T;
	tK = lzw_compress(0.1);
	tK2 = entropy_compress(0.1);
	printf("%f %f\n", (double) n2b(ALPHABET_SIZE) * tT / tK, (double) n2b(ALPHABET_SIZE) * tT / tK2);
	system("pause");
	return 0;
}

double label_edge() {
    int i, j, k, D;
    /*
		double dist;
		int id, from, to;
		struct edge *next;
	*/
	edge *buffer[maxDEG];
	long long label_count[maxDEG], sum = 0;
	for (i = 0; i < maxDEG; i ++)
		label_count[i] = 0;
    for (i = 0; i < N; i ++) {
        edge *p;
        for (D = 0, p = adj_list[i]; p != NULL; p = p->next)
			buffer[D ++] = p;
        for (j = 0; j < D; j ++)
		for (k = j + 1; k < D; k ++) {
			if (buffer[j]->count < buffer[k]->count) {
				edge *temp = buffer[j];
				buffer[j] = buffer[k];
				buffer[k] = temp;
			}
		}
		for (j = 0; j < D; j ++) {
			buffer[j]->label = j;
			label_count[j] += (long long) buffer[j]->count;
			sum += (long long) buffer[j]->count;
		}
    }
    double entropy = 0;
    for (i = 0; i < maxDEG; i ++) {
		if (label_count[i] == 0) continue;
		double p = (double) label_count[i] / sum;
		entropy += - p * log2(p);
		printf("label %d: %lld (%f, %f)\n", i, label_count[i], p, - p * log2(p));
    }
    return entropy;
}

void init(int argc, char **argv) {
	init_queue();
	init_adj_list("map\\nodeOSM.txt", "map\\edgeOSM.txt");
	init_hash();
	null = new_bst(-1, NULL);
	null->l = null->r = null;
	null->h = -1;
	null->s = 0;
	bst_count = trie_count = 0;
	ALPHABET_SIZE = 3;
	DICT_SIZE = maxD;
	dict_root = init_trie();
	sdict_root = init_trie();
	step_count = 0;
	STEP = 1000000;
	tK = tKs = tKf = tKsf = 0;
	DECODE_TEST = 1;
}

int main(int argc, char **argv) {
	init(argc, argv);
	//dijkstra_build_table("d:\\table4.txt");
	//load_table("d:\\table.txt");
	//scan_folder("data\\mm", "*.txt", direct_compress_mm_file);
	//double entropy = label_edge();
	//printf("%f, %f\n", entropy, n2b(ALPHABET_SIZE) / entropy);
	//delete_dict(dict_root);
	//delete_dict(sdict_root);
	//free(buffer); free(refer);
	return EXIT_SUCCESS;
}
