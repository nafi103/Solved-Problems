#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
const int mod = 1e9+7;
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
vector<int>index_level,level;

const int mt = 0;

struct Lazy_Segment_Tree{
    int n;
    vector<int>lazy1,lazy2,st;

    Lazy_Segment_Tree(int _n){
        n = _n;
        st.resize(4*n);
        lazy1.resize(4*n,0);
        lazy2.resize(4*n,0);
    }
    
    void propagate(int node, int b, int e){
        if(lazy1[node]==mt and lazy2[node]==mt)
            return;
        if(b!=e){
            lazy1[2*node] = (lazy1[2*node]+lazy1[node])%mod;
            lazy1[2*node+1] = (lazy1[2*node+1]+lazy1[node])%mod;
            lazy2[2*node] = (lazy2[2*node]+lazy2[node])%mod;
            lazy2[2*node+1] = (lazy2[2*node+1]+lazy2[node])%mod;
        }else{
            st[node] = (st[node]+lazy1[node])%mod;
            st[node] = (st[node]+mod-(index_level[b]*lazy2[node])%mod)%mod;
        }
        lazy1[node] = 0;
        lazy2[node] = 0;
    }
    
    void update(int node, int b, int e, int &l, int &r, int &x, int &k, int &anc){
        propagate(node, b, e);
        if(e<l or b>r) return;
        if(b>=l and e<=r){
            lazy1[node] = (x + anc*k)%mod;
            lazy2[node] = k;
            propagate(node,b,e);
            return;
        }
        int mid = (b+e)/2,left = 2*node, right = 2*node+1;
        update(left, b, mid,l,r,x,k,anc);
        update(right, mid+1,e,l,r,x,k,anc);
    }
    
    int query(int node, int b, int e, int &idx){
        propagate(node, b, e);
        if(e<idx or b>idx) return 0;
        if(b>=idx and e<=idx){
            return st[node];
        }
        int mid = (b+e)/2, left = 2*node, right = 2*node+1;
        if(idx<=mid)
            return query(left,b,mid,idx);
        return query(right,mid+1,e,idx);
    }
};

vector<vector<int>>t;
vector<int>subtree_size,start,stop;

int find_subtree_size(int node){
    subtree_size[node] = 1;
    for(auto &child: t[node])
        subtree_size[node]+=find_subtree_size(child);
    return subtree_size[node];
}

void construct(int node, int b, vector<int> &v){
    v[b] = node;
    start[node] = b;
    stop[node] = b+subtree_size[node]-1;
    int idx = b+1;
    for(auto &child: t[node]){
        construct(child,idx,v);
        idx+=subtree_size[child];
    }
}

void dfs(int node, int l){
    level[node] = l;
    for(auto &child: t[node])
        dfs(child,l+1);
}

void solve()
{
    int n;
    cin>>n;
    index_level.resize(n+1);
    level.resize(n+1);
    t.resize(n+1);
    start.resize(n+1);
    stop.resize(n+1);
    for(int i = 2; i<=n; i++){
        int p;
        cin>>p;
        t[p].push_back(i);
    }
    subtree_size.assign(n+1,0);
    dfs(1,0);
    find_subtree_size(1);
    vector<int> v(n+1);
    construct(1,1,v);
    for(int i = 1; i<=n; i++){
        index_level[i] = level[v[i]];
    }
    Lazy_Segment_Tree st(n);
    int q,node,x,k;
    cin>>q;
    while(q--){
        int t;
        cin>>t;
        if(t==1){
            cin>>node>>x>>k;
            st.update(1,1,n,start[node],stop[node],x,k,level[node]);
        }else{
            cin>>node;
            cout<<st.query(1,1,n,start[node])<<endl;
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