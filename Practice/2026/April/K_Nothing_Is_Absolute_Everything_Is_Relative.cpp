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

struct Node{
    int left, right, value;

    Node(int val = 0){
        left = val, right = val;
        value = 0;
    }
};

Node merge(Node &l, Node &r){
    Node res;
    res.value = l.value + r.value;
    res.value += abs(l.right - r.left);
    res.left = l.left;
    res.right = r.right;
    return res;
}

const int mt = 0;

struct Lazy_Segment_Tree{
    int n;
    vector<Node> st;
    vector<int>v,lazy;

    Lazy_Segment_Tree(vector<int>&_v,int _n){
        n = _n;
        st.resize(4*n);
        lazy.resize(4*n,0);
        v = _v;
        build(1,1,n);
    }
    
    void build(int node, int b, int e){
        if(b == e){
            st[node] = Node(v[b]);
            return;
        }
        int mid = (b+e)/2,left = 2 * node, right = 2*node+1;
        build(left, b, mid);
        build(right, mid + 1,e);
        st[node] = merge(st[left] , st[right]);
    }
    
    void propagate(int node, int b, int e){
        if(lazy[node]==mt)
            return;
        st[node].left += lazy[node];
        st[node].right += lazy[node];
        if(b!=e){
            lazy[2*node] += lazy[node];
            lazy[2*node+1] += lazy[node];
        }
        lazy[node] = 0;
    }
    
    void update(int node, int b, int e, int &l, int &r, int &value){
        propagate(node, b, e);
        if(e<l or b>r) return;
        if(b>=l and e<=r){
            lazy[node] = value;
            propagate(node,b,e);
            return;
        }
        int mid = (b+e)/2,left = 2*node, right = 2*node+1;
        update(left, b, mid,l,r,value);
        update(right, mid+1,e,l,r,value);
        st[node] = merge(st[left], st[right]);
    }
    
    Node query(int node, int b, int e, int &l, int &r){
        propagate(node, b, e);
        // if(e<l or b>r) return Node();
        if(b>=l and e<=r){
            return st[node];
        }
        int mid = (b+e)/2, left = 2 * node, right = 2*node+1;
        if(mid < l)
            return query(right, mid + 1, e, l, r);
        else if(mid + 1 > r)
            return query(left, b, mid, l, r);
        Node qleft = query(left,b,mid,l,r), qright = query(right,mid+1,e,l,r);
        return merge(qleft, qright);
    }

    void update(int l, int r, int val){
        update(1, 1, n, l, r, val);
    }

    int query(int l, int r){
        return query(1, 1, n, l, r).value;
    }
};

void solve()
{
    int n, q;
    cin >> n >> q;
    vector<int> arr(n + 1);
    for(int i = 1; i <= n; i++){
        cin >> arr[i];
    }
    Lazy_Segment_Tree st(arr, n);
    while(q--){
        int t;
        cin >> t;
        if(t == 1){
            int l, r, val;
            cin >> l >> r >> val;
            st.update(l, r, val);
        }else{
            int l, r;
            cin >> l >> r;
            cout << st.query(l, r) << endl;
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