#include <bits/stdc++.h>
 #include <ext/pb_ds/assoc_container.hpp>
#include <ext/pb_ds/tree_policy.hpp>
using namespace std;
  using namespace chrono;
using namespace __gnu_pbds;
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
 /*
 * Standard Segment Tree (Point Update, Range Query)
 * Time: O(N) build, O(log N) update/query
 * Use: Range Sum, Range Min/Max, Range GCD
 */
struct Node {
    int value;
    Node(int val = 0) : value(val) {} 
    // Default values: sum -> 0, min -> inf, max -> -inf
};
 Node merge(Node &left, Node &right) {
    return Node(left.value + right.value);
}
 struct Segment_Tree {
    int n;
    vector<Node> st;
     Segment_Tree(int _n) {
        n = _n;
        st.resize(4 * n);
    }
     void update(int node, int b, int e, int idx, Node &value) {
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
     void update(int id, int val){
        Node tmp(val);
        update(1, 1, n, id, tmp);
    }
     int query(int l, int r){
        return query(1, 1, n, l, r).value;
    }
};
 int expo(int a, int b){
    a %= mod;
    int res = 1;
    while(b){
        if(b & 1)
            res = (res * a) % mod;
        a = (a * a) % mod;
        b >>= 1;
    }
    return res;
}
 int inv(int a){
    return expo(a, mod - 2);
}
 void solve()
{
    int n;
    cin >> n;
    vector<int> arr(n), sarr;
    map<int,int> compressed;
    for(auto &x: arr){
        cin >> x;
    }
    compressed[0] = 0;
    sarr = arr;
    sort(all(sarr));
    for(auto &x: sarr){
        compressed[x] = sz(compressed);
    }
    Segment_Tree st(n);
    pbds<int> d;
    for(int i = 0; i < n; i++){
        d.insert(arr[i]);
        st.update(compressed[arr[i]], arr[i]);
        if(i >= 2){
            int k = i + 1;
            auto get_L = [&](int idx) -> int{
                int val = *d.find_by_order(idx);
                int sum_left = st.query(1, compressed[val] - 1);
                return idx * val - sum_left;
            };
            auto get_R = [&](int idx) -> int{
                int val = *d.find_by_order(idx);
                int sum_right = st.query(compressed[val] + 1, n);
                return sum_right - (k - 1 - idx) * val;
            };
            int low = 1, high = k - 2;
            int best_j = 1;
            while(low <= high){
                int mid = low + (high - low) / 2;
                int L_score = get_L(mid - 1);
                int R_score = get_R(mid + 1);
                if(L_score >= R_score){
                    best_j = mid;
                    high = mid - 1;
                }else{
                    low = mid + 1;
                }
            }
            int min_numerator = inf; 
            for(int j = max(1ll, best_j - 1); j <= min(k - 2, best_j + 1); j++){
                int cur_max = max(get_L(j - 1), get_R(j + 1));
                min_numerator = min(min_numerator, cur_max);
            }
            int denominator = i - 1;
            int ans = (min_numerator % mod) * inv(denominator) % mod;
            cout << ans << endl;
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
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}