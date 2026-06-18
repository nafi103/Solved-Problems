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
    int pref, suff, zero, one;
    bool flag;
     Node(){
        pref = suff = -1;
        zero = one = 0;
        flag = true;
    }
     Node(int val){
        pref = suff = val;
        flag = true;
        zero = (val == 0);
        one = (val == 1);
    }
};
 const Node mt = Node();
 Node merge(Node &left, Node &right)
{
    Node res;
    res.flag = left.flag and right.flag and left.suff != right.pref;
    res.pref = left.pref;
    res.suff = right.suff;
    res.zero = left.zero + right.zero;
    res.one = left.one + right.one;
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
     Node query(int node, int b, int e, int &l, int &r)
    {
        if (b >= l and e <= r)
        {
            return st[node];
        }
        int mid = (b + e) / 2, left = 2 * node, right = 2 * node + 1;
        if(mid < l)
            return query(right, mid + 1, e, l, r);
        if(mid + 1 > r)
            return query(left, b, mid, l, r);
        Node query_left = query(left, b, mid, l, r), query_right = query(right, mid + 1, e, l, r);
        return merge(query_left, query_right);
    }
     Node query(int l, int r){
        return query(1, 1, n, l, r);
    }
};
 void solve()
{
    int n, q;
    cin >> n >> q;
    vector<int> arr(n + 1);
    for(int i = 1; i <= n; i++)
        cin >> arr[i];
    Segment_Tree st(arr, n);
    while(q--){
        int l, r;
        cin >> l >> r;
        Node res = st.query(l, r);
        if(res.zero % 3 != 0 or res.one % 3 != 0){
            cout << -1 << endl;
        }else{
            cout << res.zero / 3 + res.one / 3 + res.flag << endl;
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
        // cout<<"Case "<<z<<": ";
        solve();
    }
}