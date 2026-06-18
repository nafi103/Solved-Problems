#include <bits/stdc++.h>
 #include <ext/pb_ds/assoc_container.hpp>
#include <ext/pb_ds/tree_policy.hpp>
 using namespace std;
using namespace __gnu_pbds;
 /*
 * PBDS (Ordered Set)
 * find_by_order(k): Returns iterator to kth element (0-indexed)
 * order_of_key(x): Returns number of elements strictly smaller than x
 */
template <class T>
using pbds = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update>;
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
        st[node] = st[left] + st[right];
    }
        void propagate(int node, int b, int e) {
        if (lazy[node] == mt) return;
        st[node] += ((e - b + 1) * lazy[node]);
        if (b != e) {
            lazy[2 * node] += lazy[node];
            lazy[2 * node + 1] += lazy[node];
        }else{
            v[b] += lazy[node];
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
        st[node] = st[left] + st[right];
    }
        int query(int node, int b, int e, int l, int r) {
        propagate(node, b, e);
        if (e < l or b > r) return 0;
        if (b >= l and e <= r) return st[node];
        int mid = (b + e) / 2, left = 2 * node, right = 2 * node + 1;
        return query(left, b, mid, l, r) + query(right, mid + 1, e, l, r);
    }
     int query(int l, int r){
        return query(1, 1, n, l, r);
    }
     void update(int l, int r, int val){
        update(1, 1, n, l, r, val);
    }
 };
 void solve()
{
    int n;
    cin >> n;
    vector<int> arr(n + 1), new_arr(n + 1);
    for(int i = 1; i <= n; i++){
        cin >> arr[i];
    }
    vector<int> v(n + 1, n);
    for(int i = 1; i <= arr[n]; i++){
        v[i]--;
    }
    Lazy_Segment_Tree st(v, n);
    int ans = 0, mn = arr[n], mx_ans = 0;
    map<int,int> id;
    id[arr[n]] = n;
    for(int i = n - 1; i >= 1; i--){
        if(arr[i] < mn){
            st.update(1, arr[i], -1);
            id[arr[i]] = i;
            mn = arr[i];
            new_arr[i] = arr[i];
        }else{
            // st.update(1, mn, -1);
            // for(int i = 1; i <= n; i++){
            //     st.query(i, i);
            // }
            // debug(st.v)
            int index_sum = st.query(1, arr[i]);
            // debug(index_sum)
            ans += (index_sum - arr[i] * i);
            // debug(ans)
            st.update(1, arr[i], -1);
            // for(int i = 1; i <= n; i++){
            //     st.query(i, i);
            // }
            // debug(st.v)
            new_arr[i] = mn;
        }
    }
    // debug(arr) debug(new_arr)
    mx_ans = ans;
    pbds<pair<int,int>> pref, suff;
    for(int i = n; i > 1; i--){
        suff.insert({arr[i], i});
    }
    pref.insert({arr[1], 1});
    for(int i = 2; i <= n; i++){
        suff.erase({arr[i], i});
        int greaterEqual = sz(suff) - suff.order_of_key({arr[i], -inf});
        int loss = n - greaterEqual - i;
        int gain = sz(pref) - pref.order_of_key({arr[i], -inf});
        mx_ans = max(mx_ans, ans + gain - loss);
        pref.insert({arr[i], i});
    }
    cout << mx_ans << endl;
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