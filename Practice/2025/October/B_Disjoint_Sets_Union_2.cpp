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

struct DSU{
    vector<int>parent, _size, mx, mn;

    DSU(int n){
        parent.resize(n);
        iota(all(parent),0);
        _size.assign(n,1); 
        mx.resize(n);
        mn.resize(n);
        iota(all(mx),0);
        iota(all(mn),0);
    }
 
    int find(int i){ 
        if(parent[i]==i) return i;
        return parent[i] = find(parent[i]); 
    } 
    
    int size(int a){ 
        a = find(a); 
        return _size[a]; 
    }

    void query(int a){
        a = find(a);
        cout<<mn[a]<<" "<<mx[a]<<" "<<_size[a]<<endl;
    }
    
    void Union(int a, int b){ 
        a = find(a); 
        b = find(b); 
        if(a==b) return; 
        if(_size[a]<_size[b]) swap(a,b);
        parent[b] = a; 
        _size[a]+=_size[b];
        mx[a] = max(mx[a],mx[b]);
        mn[a] = min(mn[a],mn[b]);
    }
};

void solve()
{
    int n,q;
    cin>>n>>q;
    DSU uf(n+1);
    while(q--){
        string op;
        cin>>op;
        if(op=="get"){
            int u;
            cin>>u;
            uf.query(u);
        }else{
            int u,v;
            cin>>u>>v;
            uf.Union(u,v);
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