#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 998244353;
const int inf = 1e18 + 10;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

struct Node
{
    int sum, pref, suff, value;

    Node(){
        sum = pref = suff = value = 0;
    }

    Node(int x){
        sum = x;
        pref = suff = value = max(0ll, x);
    }
};

Node merge(Node &left, Node &right)
{
    Node res;
    res.sum = left.sum + right.sum;
    res.pref = max(left.pref, left.sum + right.pref);
    res.suff = max(right.suff, right.sum + left.suff);
    res.value = max({left.value, right.value, left.suff + right.pref});
    return res;
}

struct Segment_Tree
{
    int n;
    vector<int> v;
    vector<Node> st;

    Segment_Tree(vector<int> &_v, int _n)
    {
        n = _n;
        st.resize(4 * n);
        v = _v;
        build(1, 1, n);
    }

    void build(int node, int b, int e)
    {
        if (b == e)
        {
            st[node] = Node(v[b]);
            return;
        }
        int mid = (b + e) / 2, left = 2 * node, right = 2 * node + 1;
        build(left, b, mid);
        build(right, mid + 1, e);
        st[node] = merge(st[left], st[right]);
    }

    void update(int node, int b, int e, int &idx, Node &value)
    {
        if (e < idx or b > idx)
            return;
        if (b == idx and e == idx)
        {
            st[node] = value;
            return;
        }
        int mid = (b + e) / 2, left = 2 * node, right = 2 * node + 1;
        update(left, b, mid, idx, value);
        update(right, mid + 1, e, idx, value);
        st[node] = merge(st[left], st[right]);
    }

    Node query(int node, int b, int e, int &l, int &r)
    {
        if (e < l or b > r)
            return Node();
        if (b >= l and e <= r)
        {
            return st[node];
        }
        int mid = (b + e) / 2, left = 2 * node, right = 2 * node + 1;
        Node query_left = query(left, b, mid, l, r), query_right = query(right, mid + 1, e, l, r);
        return merge(query_left, query_right);
    }

    int query(int l, int r){
        return query(1, 1, n, l, r).value;
    }

    void update(int id, int value){
        Node tmp(value);
        update(1, 1, n, id, tmp);
    }
};

void solve()
{
    int n, k, x;
    cin >> n >> k >> x;
    vector<int> v(n + 1);
    for(int i = 1; i <= n; i++)
        cin >> v[i];
    if(x < 0){
        x = -x;
        k = n - k;
    }
    for(int i = 1; i <= k; i++){
        v[i] += x;
    }
    for(int i = k + 1; i <= n; i++){
        v[i] -= x;
    }
    Segment_Tree st(v, n);
    int ans = st.query(1, n);
    for(int i = k + 1; i <= n; i++){
        v[i] += 2 * x;
        v[i - k] -= 2 * x;
        st.update(i - k, v[i - k]);
        st.update(i, v[i]);
        ans = max(ans, st.query(1, n));
    }
    cout << ans << endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}