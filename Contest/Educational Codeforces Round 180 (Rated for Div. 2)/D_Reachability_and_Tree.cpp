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
vector<vector<int>>t;
vector<pair<int,int>>edges;
vector<int>parent;

void dfs(int node, int par, int col){
    parent[node] = par;
    for(auto &child: t[node]){
        if(child!=par){
            if(col){
                edges.push_back({child,node});
            }else{
                edges.push_back({node,child});
            }
            dfs(child,node,col^1);
        }
    }
}

void solve()
{
    edges.clear();
    parent.clear();
    t.clear();
    int n;
    cin>>n;
    t.resize(n+1);
    parent.resize(n+1);
    for(int i = 1; i<n; i++){
        int u,v;
        cin>>u>>v;
        t[u].push_back(v);
        t[v].push_back(u);
    }
    int src = -1;
    for(int i = 1; i<=n; i++){
        if(sz(t[i])==2){
            src = i;
            break;
        }
    }
    if(src==-1){
        cout<<"NO"<<endl;
        return;
    }
    cout<<"YES"<<endl;
    edges.push_back({src,t[src][0]});
    edges.push_back({t[src][1],src});
    dfs(t[src][0],src,1);
    dfs(t[src][1],src,0);
    for(auto &[f,s]: edges){
        cout<<f<<" "<<s<<endl;
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
    cin >> t;
    for(int z = 1; z<=t; z++){
        // cout<<"Case "<<z<<": ";
        solve();
    }
}