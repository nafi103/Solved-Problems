#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 998244353;
const int inf = 1e9 + 10;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

/*
 * Segment Tree with Lazy Propagation (Range Update, Range Query)
 * Time: O(N) build, O(log N) update/query
 * Use: Range Add, Range Sum
 */
const int mt = 0; // marker value for lazy

struct Min_Lazy_Segment_Tree {
    int n;
    vector<int> lazy, st;

    Min_Lazy_Segment_Tree(vector<int>&_v, int _n) {
        n = _n;
        st.resize(4 * n);
        lazy.resize(4 * n, 0);
        build(1, 1, n, _v);
    }
    
    void build(int node, int b, int e, vector<int> &v) {
        if (b == e) {
            st[node] = v[b];
            return;
        }
        int mid = (b + e) / 2, left = 2 * node, right = 2 * node + 1;
        build(left, b, mid, v);
        build(right, mid + 1, e, v);
        st[node] = min(st[left], st[right]);
    }
    
    void propagate(int node, int b, int e) {
        if (lazy[node] == mt) return;
        st[node] += lazy[node];
        if (b != e) {
            lazy[2 * node] += lazy[node];
            lazy[2 * node + 1] += lazy[node];
        }
        lazy[node] = 0;
    }
    
    void update(int node, int b, int e, int l, int r, int value) {
        propagate(node, b, e);
        if (e < l or b > r) return;
        if (b >= l and e <= r) {
            lazy[node] = value;
            propagate(node, b, e);
            return;
        }
        int mid = (b + e) / 2, left = 2 * node, right = 2 * node + 1;
        update(left, b, mid, l, r, value);
        update(right, mid + 1, e, l, r, value);
        st[node] = min(st[left], st[right]);
    }
    
    int query(int node, int b, int e, int l, int r) {
        propagate(node, b, e);
        if (e < l or b > r) return inf;
        if (b >= l and e <= r) return st[node];
        int mid = (b + e) / 2, left = 2 * node, right = 2 * node + 1;
        return min(query(left, b, mid, l, r), query(right, mid + 1, e, l, r));
    }

    int query(int l, int r){
        return query(1, 1, n, l, r);
    }

    void update(int l, int r, int value){
        update(1, 1, n, l, r, value);
    }
};

struct Max_Lazy_Segment_Tree {
    int n;
    vector<int> lazy, st;

    Max_Lazy_Segment_Tree(vector<int>&_v, int _n) {
        n = _n;
        st.resize(4 * n);
        lazy.resize(4 * n, 0);
        build(1, 1, n, _v);
    }
    
    void build(int node, int b, int e, vector<int> &v) {
        if (b == e) {
            st[node] = v[b];
            return;
        }
        int mid = (b + e) / 2, left = 2 * node, right = 2 * node + 1;
        build(left, b, mid, v);
        build(right, mid + 1, e, v);
        st[node] = max(st[left], st[right]);
    }
    
    void propagate(int node, int b, int e) {
        if (lazy[node] == mt) return;
        st[node] += lazy[node];
        if (b != e) {
            lazy[2 * node] += lazy[node];
            lazy[2 * node + 1] += lazy[node];
        }
        lazy[node] = 0;
    }
    
    void update(int node, int b, int e, int l, int r, int value) {
        propagate(node, b, e);
        if (e < l or b > r) return;
        if (b >= l and e <= r) {
            lazy[node] = value;
            propagate(node, b, e);
            return;
        }
        int mid = (b + e) / 2, left = 2 * node, right = 2 * node + 1;
        update(left, b, mid, l, r, value);
        update(right, mid + 1, e, l, r, value);
        st[node] = max(st[left], st[right]);
    }
    
    int query(int node, int b, int e, int l, int r) {
        propagate(node, b, e);
        if (e < l or b > r) return inf;
        if (b >= l and e <= r) return st[node];
        int mid = (b + e) / 2, left = 2 * node, right = 2 * node + 1;
        return max(query(left, b, mid, l, r), query(right, mid + 1, e, l, r));
    }

    int query(int l, int r){
        return query(1, 1, n, l, r);
    }

    void update(int l, int r, int value){
        update(1, 1, n, l, r, value);
    }
};

void solve()
{
    int n, m;
    cin >> n >> m;

    vector<int> arr(n + 1);
    vector<pair<int,int>> seg(m);
    vector<vector<int>> add(n + 1), rmv(n + 1);
    for(int i = 1; i <= n; i++){
        cin >> arr[i];
    }

    for(int i = 0; i < m; i++){
        auto &[l, r] = seg[i];
        cin >> l >> r;
        add[l].push_back(r);
        rmv[r].push_back(l);
    }

    Min_Lazy_Segment_Tree mnst(arr, n);
    Max_Lazy_Segment_Tree mxst(arr, n);

    int ans = *max_element(arr.begin() + 1, arr.end()) - *min_element(arr.begin() + 1, arr.end()), id = -1;
    debug(ans)
    for(int i = 1; i <= n; i++){
        for(auto &r: add[i]){
            mnst.update(i, r, -1);
            mxst.update(i, r, -1);
        }

        int mn = mnst.query(1, n), mx = mxst.query(1, n);
        if(mx - mn > ans){
            ans = mx - mn;
            id = i;
        }

        for(auto &l: rmv[i]){
            mnst.update(l, i, 1);
            mxst.update(l, i, 1);
        }
    }

    if(id == -1){
        cout << ans << endl;
        cout << 0 << endl;
        return;
    }

    cout << ans << endl;
    vector<int> take;
    for(int i = 0; i < m; i++){
        auto &[l, r] = seg[i];
        if(l <= id and r >= id){
            take.push_back(i + 1);
        }
    }
    cout << sz(take) << endl;
    for(auto &x: take){
        cout << x << " ";
    }
    cout << endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}