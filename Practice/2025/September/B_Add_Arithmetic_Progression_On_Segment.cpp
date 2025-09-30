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

struct Lazy_Segment_Tree{
    int n;
    vector<int>v,lazy1,lazy2,st;

    Lazy_Segment_Tree(int _n){
        n = _n;
        st.resize(4*n,0);
        lazy1.assign(4*n,0);
        lazy2.assign(4*n,0);
    }
    
    void propagate(int node, int b, int e){
        if(lazy1[node]==0 and lazy2[node]==0)
            return;
        if(b!=e){
            lazy1[2*node] += lazy1[node];
            lazy1[2*node+1] += lazy1[node];
            lazy2[2*node] += lazy2[node];
            lazy2[2*node+1] += lazy2[node];
        }else{
            st[node] += lazy1[node];
            st[node] += lazy2[node]*b;
        }
        lazy1[node] = 0;
        lazy2[node] = 0;
    }
    
    void update(int node, int b, int e, int &l, int &r, int &a, int &d){
        propagate(node, b, e);
        if(e<l or b>r) return;
        if(b>=l and e<=r){
            lazy1[node] += a-d*l;
            lazy2[node] += d;
            propagate(node,b,e);
            return;
        }
        int mid = (b+e)/2,left = 2*node, right = 2*node+1;
        update(left, b, mid,l,r,a,d);
        update(right, mid+1,e,l,r,a,d);
    }
    
    int query(int node, int b, int e, int &idx){
        propagate(node, b, e);
        if(e<idx or b>idx) return 0;
        if(b>=idx and e<=idx){
            return st[node];
        }
        int mid = (b+e)/2, left = 2*node, right = 2*node+1;
        return query(left,b,mid,idx) + query(right,mid+1,e,idx);
    }
};

void solve()
{
    int n,m;
    cin>>n>>m;
    Lazy_Segment_Tree st(n);
    while(m--){
        int t;
        cin>>t;
        if(t==1){
            int l,r,a,d;
            cin>>l>>r>>a>>d;
            st.update(1,1,n,l,r,a,d);
        }else{
            int i;
            cin>>i;
            cout<<st.query(1,1,n,i)<<endl;
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