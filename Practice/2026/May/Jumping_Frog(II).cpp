#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 998244353;
const int inf = 1e12 + 10;

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

struct Lazy_Segment_Tree {
    int n;
    vector<int> v, lazy, st;

    Lazy_Segment_Tree(int _n) {
        n = _n;
        st.assign(4 * n, 0);
        lazy.resize(4 * n, 0);
    }
    
    void propagate(int node, int b, int e) {
        if (lazy[node] == mt) return;
        st[node] += lazy[node];
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

    void update(int l, int r, int val){
        if(l > r)
            return;
        r = min(r, n);
        update(1, 1, n, l, r, val);
    }

    int query(int l, int r){
        if(l > n)
            return inf;
        return query(1, 1, n, l, r);
    }
};

void solve()
{
    int n, q;
    cin >> n >> q;
    Lazy_Segment_Tree st(n);
    vector<int> arr(n + 1);
    for(int i = 1; i <= n; i++){
        cin >> arr[i];
        st.update(i, i + arr[i] - 1, 1);
    }
    while(q--){
        int t;
        cin >> t;
        if(t == 2){
            int s;
            cin >> s;
            if(s == 0){
                cout << "no" << endl;
                continue;
            }
            if(st.query(s, n) == 0){
                cout << "no" << endl;
            }else{
                cout << "yes" << endl;
            }
        }else{
            int p, s;
            cin >> p >> s;
            st.update(p, p + arr[p] - 1, -1);
            arr[p] = s;
            st.update(p, p + arr[p] - 1, 1);
        }
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
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        cout<<"Case "<<z<<":\n";
        solve();
    }
}