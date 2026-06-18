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
 //type 1 -> gcd, type 0 -> mn
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
     Node query(int node, int b, int e, int &l, int &r)
    {
        if (e < l or b > r){
            return Node();
        }
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
};
 const int mt = -1;
 struct Lazy_Segment_Tree{
    int n;
    vector<int>v,lazy,st;
     Lazy_Segment_Tree(int _n){
        n = _n;
        st.resize(4*n);
        lazy.assign(4*n,mt);
        v.assign(n + 1, true);
        build(1, 1, n);
    }
        void build(int node, int b, int e){
        if(b==e){
            st[node] = v[b];
            return;
        }
        int mid = (b+e)/2,left = 2*node, right = 2*node+1;
        build(left, b, mid);
        build(right, mid+1,e);
        st[node] = st[left]+st[right];
    }
        void propagate(int node, int b, int e){
        if(lazy[node]==mt)
            return;
        st[node] = ((e - b + 1)*lazy[node]);
        if(b != e){
            lazy[2*node] = lazy[node];
            lazy[2*node+1] = lazy[node];
        }
        lazy[node] = mt;
    }
        void update(int node, int b, int e, int &l, int &r, int &value){
        propagate(node, b, e);
        if(e < l or b > r) return;
        if(b>=l and e<=r){
            lazy[node] = value;
            propagate(node,b,e);
            return;
        }
        int mid = (b+e)/2,left = 2*node, right = 2*node+1;
        update(left, b, mid,l,r,value);
        update(right, mid+1,e,l,r,value);
        st[node] = st[left]+st[right];
    }
        int query(int node, int b, int e, int &l, int &r){
        propagate(node, b, e);
        if(e<l or b>r) return 0;
        if(b>=l and e<=r){
            return st[node];
        }
        int mid = (b+e)/2, left = 2*node, right = 2*node+1;
        return query(left,b,mid,l,r) + query(right,mid+1,e,l,r);
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
    int n, p, ans = 0;
    cin >> n >> p;
     vector<int> visited(n, false);
    vector<int> arr(n + 1);
    vector<pair<int,int>> order(n);
     for(int i = 1; i <= n; i++){
        cin >> arr[i];
        order[i - 1] = {arr[i], i};
    }
     sort(all(order));
     Segment_Tree g_st(arr, n);
    Lazy_Segment_Tree st(n);
     int rem_edges = n - 1;
    for(auto &[g, i]: order){
        if(g > p)
            continue;
        //right
        int right = i, l = i + 1, r = n;
        while(l <= r){
            int mid = (l + r) / 2;
            int new_g = g_st.query(i, mid);
            if(g == new_g){
                l = mid + 1;
                right = max(right, mid);
            }else{
                r = mid - 1;
            }
        }
        //left
        int left = i;
        l = 1, r = i;
        while(l <= r){
            int mid = (l + r) / 2;
            int new_g = g_st.query(mid, i);
            if(g == new_g){
                r = mid - 1;
                left = min(left, mid);
            }else{
                l = mid + 1;
            }
        }
        // merge
        if(left < right){
            int can_connect = st.query(left, right - 1);
            ans += g * can_connect;
            rem_edges -= can_connect;
            if(can_connect > 0){
                st.update(left, right - 1, 0);
            }
        }
    }
    cout << ans + rem_edges * p << endl;
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