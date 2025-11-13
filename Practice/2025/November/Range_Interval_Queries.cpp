#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define pi acos(-1.0)
const int mod = 998244353;
#define inf 1e18 + 10
#define sz(x) (int)(x).size()
#define LSOne(x) ((x) & (-x))
#define all(x) x.begin(), x.end()
#define endl "\n"

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x)                                        \
    cerr << "Line " << __LINE__ << ": " << #x << " = "; \
    _print(x);                                          \
    cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

struct Node
{
    vector<int> v;
    Node()
    {
        v.clear();
    }
    Node(int n)
    {
        v = {n};
    }
};

void combine(Node &a, Node &b, Node &res)
{
    res.v.clear();
    res.v.reserve(sz(a.v) + sz(b.v));
    merge(all(a.v), all(b.v), back_inserter(res.v));
}

struct Merge_Sort_Tree
{
    vector<int> v;
    vector<Node> t;

    Merge_Sort_Tree(int n, vector<int> &_v)
    {
        t.resize(4 * n);
        v = _v;
        build(1, 1, n);
    }

    void build(int node, int b, int e)
    {
        if (b == e)
        {
            t[node] = Node(v[b]);
            return;
        }
        int mid = (b + e) / 2, left = 2 * node, right = 2 * node + 1;
        build(left, b, mid);
        build(right, mid + 1, e);
        combine(t[left], t[right], t[node]);
    }

    int query(int node, int b, int e, int &l, int &r, int &c, int &d)
    {
        if (b > r or e < l)
            return 0;
        if (b >= l and e <= r)
            return upper_bound(all(t[node].v), d) - lower_bound(all(t[node].v), c);
        int mid = (b + e) / 2, left = 2 * node, right = 2 * node + 1;
        return query(left, b, mid, l, r, c, d) + query(right, mid + 1, e, l, r, c, d);
    }
};

void solve()
{
    int n, m;
    scanf("%d%d", &n, &m);
    vector<int> v(n + 1);
    for (int i = 1; i <= n; i++)
    {
        scanf("%d", &v[i]);
    }
    Merge_Sort_Tree mst(n, v);
    while (m--)
    {
        int l, r, a, b;
        scanf("%d%d%d%d", &l, &r, &a, &b);
        printf("%d\n", mst.query(1, 1, n, l, r, a, b));
    }
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    // ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    // cout.precision(10);
    // cout.setf(ios::fixed);
    int t = 1;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}