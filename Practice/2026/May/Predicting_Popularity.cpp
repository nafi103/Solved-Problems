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
const int mt = 0;

struct Lazy_Segment_Tree {
    int n;
    vector<int> v, lazy, st;

    Lazy_Segment_Tree(vector<int>& _v, int _n) {
        n = _n;
        st.resize(4 * n);
        lazy.resize(4 * n, 0);
        v = _v;
        build(1, 1, n);
    }
    
    void build(int node, int b, int e) {
        if (b == e) {
            st[node] = v[b];
            return;
        }
        int mid = (b + e) / 2, left = 2 * node, right = 2 * node + 1;
        build(left, b, mid);
        build(right, mid + 1, e);
        st[node] = min(st[left], st[right]);
    }
    
    void propagate(int node, int b, int e) {
        if (lazy[node] == mt) return;
        st[node] += lazy[node];
        if(b == e)
            v[b] += lazy[node];
        if (b != e) {
            lazy[2 * node] += lazy[node];
            lazy[2 * node + 1] += lazy[node];
        }
        lazy[node] = mt;
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
};


template <typename T>
struct Fenwick_Tree{
    int n;
    vector<T> bit;

    Fenwick_Tree(int _n) : n(_n), bit(_n, 0) {}

    Fenwick_Tree(const vector<T> &arr){
        n = sz(arr);
        bit.assign(n, 0);
        for (int i = 0; i < n; i++){
            bit[i] += arr[i];
            int r = i | (i + 1);
            if(r < n)
                bit[r] += bit[i];
        }
    }

    T query(int r) const {
        T sum = 0;
        for(; r >= 0; r = (r & (r + 1)) - 1)
            sum += bit[r];
        return sum;
    }

    T query(int l, int r) const {
        if(l > r)
            return 0;
        return query(r) - query(l - 1);
    }

    void add(int idx, T delta){
        for(; idx < n; idx = idx | (idx + 1)){
            bit[idx] += delta;
        }
    }
};

// const int N = 2000000;
const int N = 30;

void solve()
{
    int ac, dr;
    cin >> ac >> dr;
    int n, m;
    cin >> n;
    vector<int> a(n), d(n);
    for(int i = 0; i < n; i++){
        cin >> a[i];
        a[i] = max(0, a[i] - ac);
    }
    for(int i = 0; i < n; i++){
        cin >> d[i];
        d[i] = max(0, d[i] - dr);
    }

    Fenwick_Tree<int> ft(N + 1);
    vector<int> v(N + 1);
    for(int i = 0; i < n; i++){
        v[a[i] + d[i] + 1]++;
        ft.add(a[i] + d[i], 1);
    }
    for(int i = 2; i <= N; i++){
        v[i] += (v[i - 1] - 1);
    }
    // debug(a) debug(d)
    // debug(v)

    Lazy_Segment_Tree st(v, N);

    cin >> m;
    while(m--){
        int i, ax, dx;
        cin >> i >> ax >> dx;
        i--;
        ft.add(a[i] + d[i], -1);
        st.update(1, 1, N, a[i] + d[i] + 1, N , -1);
        a[i] = max(0, ax - ac);
        d[i] = max(0, dx - dr);
        st.update(1, 1, N, a[i] + d[i] + 1, N , 1);
        ft.add(a[i] + d[i], 1);

        debug(a) debug(d)
        for(int i = 1; i <= N; i++){
            st.query(1, 1, N, i, i);
        }
        debug(st.v)

        int l = 1, r = N, ans = ft.query(0);
        while(l <= r){
            int mid = (l + r) / 2, q = st.query(1, 1, N, 1, mid);
            if(q > 0){
                ans = ft.query(mid);
                l = mid + 1;
            }else{
                r = mid - 1;
            }
        }
        cout << ans << endl;
    }
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