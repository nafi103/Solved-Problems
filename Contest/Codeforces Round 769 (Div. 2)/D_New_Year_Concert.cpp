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
    int value;
     Node(int val = 0) : value(val) {}
};
 Node merge(Node &left, Node &right)
{
    return Node(gcd(left.value, right.value));
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
     void update(int i, int val){
        Node tmp = Node(val);
        update(1, 1, n, i, tmp);
    }
     int query(int l, int r){
        return query(1, 1, n, l, r).value;
    }
};
 void solve()
{
    int n;
    cin >> n;
    vector<int> arr(n + 1);
    for(int i = 1; i <= n; i++){
        cin >> arr[i];
    }
    Segment_Tree st(arr, n);
    vector<int> ans(n + 1);
    for(int i = 1; i <= n; i++){
        if(ans[i] == 0){
            int l = i, r = n;
            while(l <= r){
                int mid = (l + r) / 2;
                int g = st.query(i, mid);
                if(g > mid - i + 1)
                    l = mid + 1;
                else
                    r = mid - 1;
            }
            if(l <= n){
                int g = st.query(i, l);
                if(g == l - i + 1){
                    ans[l] = 1;
                    st.update(l, mod);
                }
            }
        }
        ans[i] += ans[i - 1];
        cout << ans[i] << (i == n ? '\n' : ' ');
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