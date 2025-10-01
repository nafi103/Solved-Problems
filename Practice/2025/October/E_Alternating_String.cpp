#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
const int mod = 998244353;
#define inf 1e18+10
#define sz(x) (int)(x).size()
#define LSOne(x) ((x)&(-x))
#define all(x) x.begin(), x.end()
#define readv(v)      \
    for (auto &x : v) \
    cin >> x
#define endl "\n"
#define fastIO ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr)
template <class T> using pbds = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update >;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

const bool mt = false;

struct Node{
    bool left_bit = 0, right_bit = 0;
    bool good = true;
    bool empty = true;
    Node(){}
    Node(bool x){
        left_bit = right_bit = x;
        good = true;
        empty = false;
    }
    void flip(){
        if(empty) return;
        left_bit^=1;
        right_bit^=1;
    }
};

void _print(Node &x){
    cerr<<x.left_bit<<" "<<x.right_bit<<" "<<x.good<<endl;
}

Node combine(Node &a, Node &b){
    if(a.empty) return b;
    if(b.empty) return a;
    Node res;
    res.empty = false;
    res.good = (a.good and b.good and(a.right_bit!=b.left_bit));
    res.left_bit = a.left_bit;
    res.right_bit = b.right_bit;
    return res;
}

struct Lazy_Segment_Tree{
    int n;
    vector<bool> lazy,v;
    vector<Node>st;

    Lazy_Segment_Tree(vector<bool>&_v,int _n){
        n = _n;
        st.resize(4*n);
        lazy.assign(4*n,0);
        v = _v;
        build(1,1,n);
    }
    
    void build(int node, int b, int e){
        if(b==e){
            st[node] = Node(v[b]);
            return;
        }
        int mid = (b+e)/2,left = 2*node, right = 2*node+1;
        build(left, b, mid);
        build(right, mid+1,e);
        st[node] = combine(st[left],st[right]);
    }
    
    void propagate(int node, int b, int e){
        if(lazy[node]==mt)
            return;
        st[node].flip();
        if(b!=e){
            lazy[2*node]  = lazy[2*node] ^ 1;
            lazy[2*node+1] = lazy[2*node+1] ^ 1;
        }
        lazy[node] = false;
    }
    
    void update(int node, int b, int e, int &l, int &r){
        propagate(node, b, e);
        if(e<l or b>r) return;
        if(b>=l and e<=r){
            lazy[node] = 1;
            propagate(node,b,e);
            return;
        }
        int mid = (b+e)/2,left = 2*node, right = 2*node+1;
        update(left, b, mid,l,r);
        update(right, mid+1,e,l,r);
        st[node] = combine(st[left],st[right]);
    }
    
    Node query(int node, int b, int e, int &l, int &r){
        propagate(node,b,e);
        if(r < b or e < l) return Node();
        if(l <= b && e <= r) return st[node];
        int mid = (b+e)/2, left = 2*node, right = 2*node+1;
        Node L = query(left,b,mid,l,r);
        Node R = query(right,mid+1,e,l,r);
        return combine(L,R);
    }
};

void solve()
{
    int n,q;
    cin>>n>>q;
    vector<bool>v(n+1);
    char c;
    for(int i = 1; i<=n; i++){
        cin>>c;
        v[i] = c-'0';
    }
    Lazy_Segment_Tree st(v,n);
    int t,l,r;
    while(q--){
        cin>>t>>l>>r;
        if(t==1){
            st.update(1,1,n,l,r);
        }else{
            if(st.query(1,1,n,l,r).good){
                cout<<"Yes"<<endl;
            }else{
                cout<<"No"<<endl;
            }
        }
    }
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    for(int z = 1; z<=t; z++){
        // cout<<"Case "<<z<<": ";
        solve();
    }
}