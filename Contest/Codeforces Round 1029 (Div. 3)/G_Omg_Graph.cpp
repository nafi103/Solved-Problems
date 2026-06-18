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
vector<vector<pair<int,int>>>g;

struct DSU{
    vector<int>parent, _size, mn, mx;
    
    DSU(int n){
        parent.resize(n);
        iota(all(parent),0);
        _size.assign(n,1); 
        mn.assign(n,inf);
        mx.assign(n,-inf);
    }
    
    int find(int i){ 
        if(parent[i]==i) return i; 
        return parent[i] = find(parent[i]); 
    }
    
    int size(int a){ 
        a = find(a); 
        return _size[a];
    }
    
    void Union(int a, int b, int w){ 
        a = find(a); 
        b = find(b); 
        if(a==b) return; 
        if(_size[a]<_size[b]) swap(a,b);
        parent[b] = a;
        _size[a]+=_size[b];
        mn[a] = min({mn[a],mn[b],w});
        mx[a] = max({mx[a],mx[b],w});
    }
};

void solve()
{
    g.clear();
    int n, m, ans = inf;
    cin>>n>>m;
    g.resize(n+1);
    vector<array<int,3>>edges(m);
    for(int i = 0; i<m; i++){
        int u,v,w;
        cin>>u>>v>>w;
        if(u>v)
            swap(u,v);
        edges[i] = {u,v,w};
    }
    sort(all(edges),[&](array<int,3>&a, array<int,3>&b){
        if(a[2]!=b[2])
            return a[2]<b[2];
        return a[0]<b[0];
    });
    DSU uf(n+1);
    for(auto &[u,v,w]: edges){
        uf.Union(u,v,w);
        if(uf.find(1)==uf.find(n)){
            int p = uf.find(1);
            ans = min(ans,uf.mn[p]+uf.mx[p]);
        }
    }
    cout<<ans<<endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    cin >> t;
    for(int z = 1; z<=t; z++){
        // cout<<"Case "<<z<<": ";
        solve();
    }
}