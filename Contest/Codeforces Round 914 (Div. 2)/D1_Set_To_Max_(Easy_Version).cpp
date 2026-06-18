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
 /*
 * Standard Segment Tree (Point Update, Range Query)
 * Time: O(N) build, O(log N) update/query
 * Use: Range Sum, Range Min/Max, Range GCD
 */
 struct Min_Segment_Tree {
     struct Node {
        int value;
        Node(int val = inf) : value(val) {} 
    };
     Node merge(const Node &left, const Node &right) {
        return Node(min(left.value, right.value));
    }
     int n;
    vector<Node> st;
     Min_Segment_Tree(const vector<int> &v, int _n) {
        n = _n;
        st.resize(4 * n + 1);
        build(1, 1, n, v);
    }
     void build(int node, int b, int e, const vector<int> &v) {
        if (b == e) {
            st[node] = Node(v[b]);
            return;
        }
        int mid = (b + e) / 2, left = 2 * node, right = 2 * node + 1;
        build(left, b, mid, v);
        build(right, mid + 1, e, v);
        st[node] = merge(st[left], st[right]);
    }
     void update(int node, int b, int e, int idx, const Node &value) {
        if (e < idx or b > idx) return;
        if (b == idx and e == idx) {
            st[node] = value;
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
        return query(1, 1, n, l, r).value;
    }
     void update(int idx, int value){
        Node tmp = Node(value);
        update(1, 1, n, idx, tmp);
    }
};
 struct Max_Segment_Tree {
     struct Node {
        int value;
        Node(int val = -inf) : value(val) {} 
    };
     Node merge(const Node &left, const Node &right) {
        return Node(max(left.value, right.value));
    }
     int n;
    vector<Node> st;
     Max_Segment_Tree(const vector<int> &v, int _n) {
        n = _n;
        st.resize(4 * n + 1);
        build(1, 1, n, v);
    }
     void build(int node, int b, int e, const vector<int> &v) {
        if (b == e) {
            st[node] = Node(v[b]);
            return;
        }
        int mid = (b + e) / 2, left = 2 * node, right = 2 * node + 1;
        build(left, b, mid, v);
        build(right, mid + 1, e, v);
        st[node] = merge(st[left], st[right]);
    }
     void update(int node, int b, int e, int idx, const Node &value) {
        if (e < idx or b > idx) return;
        if (b == idx and e == idx) {
            st[node] = value;
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
        return query(1, 1, n, l, r).value;
    }
     void update(int idx, int value){
        Node tmp = Node(value);
        update(1, 1, n, idx, tmp);
    }
};
 void solve()
{
    int n;
    cin >> n;
    vector<int> a(n + 1), b(n + 1);
    for(int i = 1; i <= n; i++)
        cin >> a[i];
    for(int i = 1; i <= n; i++)
        cin >> b[i];
     vector<vector<int>> pos(n + 2);
    for(int i = 1; i <= n; i++){
        if(a[i] > b[i]){
            cout << "NO" << endl;
            return;
        }
        pos[a[i]].push_back(i);
    }
     Max_Segment_Tree mxst(a, n);
    Min_Segment_Tree mnst(b, n);
     for(int i = 1; i <= n; i++){
         if(a[i] == b[i])
            continue;
         bool flag = false;
        int &val = b[i];
        auto left_it = upper_bound(all(pos[val]), i);
         if(left_it != pos[val].begin()){
            left_it--;
            int l = *left_it;
             if(mnst.query(l, i) >= val and mxst.query(l, i) == val)
                flag = true;
        }
         auto right_it = upper_bound(all(pos[val]), i);
        if(right_it != pos[val].end()){
            int r = *right_it;
             if(mnst.query(i, r) >= val and mxst.query(i, r) == val)
                flag = true;
        }
         if(!flag){
            cout << "NO" << endl;
            return;
        }
    }
     cout << "YES" << endl;
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