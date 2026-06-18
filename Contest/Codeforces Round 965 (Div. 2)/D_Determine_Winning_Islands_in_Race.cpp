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
 const int N = 2e5 + 10;
vector<vector<int>> g(N);
 /*
 * Standard Segment Tree (Point Update, Range Query)
 * Time: O(N) build, O(log N) update/query
 * Use: Range Sum, Range Min/Max, Range GCD
 */
 struct Segment_Tree {
     struct Node {
        int value;
        Node(int val = inf) : value(val) {} 
        // Default values: sum -> 0, min -> inf, max -> -inf
    };
     Node merge(const Node &left, const Node &right) {
        return Node(min(left.value, right.value));
    }
     int n;
    vector<int> v;
    vector<Node> st;
     Segment_Tree(int _n) {
        n = _n;
        v.assign(n + 1, inf);
        st.assign(4 * n + 1, inf);
    }
     void update(int node, int b, int e, int idx, const Node &value) {
        if (e < idx or b > idx) return;
        if (b == idx and e == idx) {
            if(v[b] > value.value){
                v[b] = value.value;
                st[node] = value;
            }
            return;
        }
        int mid = (b + e) / 2, left = 2 * node, right = 2 * node + 1;
        update(left, b, mid, idx, value);
        update(right, mid + 1, e, idx, value);
        st[node] = merge(st[left], st[right]);
    }
     Node query(int node, int b, int e, int l, int r) {
        if (e < l or b > r) return Node();
        if (b >= l and e <= r) return st[node];
        int mid = (b + e) / 2, left = 2 * node, right = 2 * node + 1;
        Node query_left = query(left, b, mid, l, r);
        Node query_right = query(right, mid + 1, e, l, r);
        return merge(query_left, query_right);
    }
     int query(int l, int r){
        if(l > r)
            return inf;
        return query(1, 1, n, l, r).value;
    }
     void update(int idx, int value){
        Node tmp = Node(value);
        update(1, 1, n, idx, tmp);
    }
};
 void solve()
{
    int n, m;
    cin >> n >> m;
     for(int i = 1; i <= n; i++){
        g[i].clear();
    }
     for(int u = 1; u < n; u++){
        g[u].push_back(u + 1);
    }
     while(m--){
        int u, v;
        cin >> u >> v;
        if(u > v)
            swap(u, v);
        g[u].push_back(v);
    }
     vector<int> d(n + 1, inf);
    d[1] = 0;
    queue<pair<int,int>> q;
    q.push({1, 0});
    while(!q.empty()){
        auto [node, dis] = q.front();
        q.pop();
        for(auto &adj: g[node]){
            if(d[adj] > dis + 1){
                d[adj] = dis + 1;
                q.push({adj, d[adj]});
            }
        }
    }
     Segment_Tree st(n);
    for(int node = 1; node < n; node++){
        int q = st.query(node + 2, n);
        if(q - (n - node - 2) <= 1)
            cout << 0;
        else
            cout << 1;
        for(auto &adj: g[node]){
            st.update(adj, d[node] + 1 + n - adj);
        }
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
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}