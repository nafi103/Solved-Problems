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
int expo(int a, int b, int m) {int res = 1; while (b > 0) {if (b & 1)res = (res * a) % m; a = (a * a) % m; b = b >> 1;} return res;}

vector<vector<int>>t;

void dfs(int node, int par, vector<int>&parent){
    parent[node] = par;
    for(auto &x: t[node]){
        if(x!=par){
            dfs(x,node,parent);
        }
    }
}

void solve()
{
    t.clear();
    int n;
    cin>>n;
    t.resize(n+1);
    for(int i = 1; i<n; i++){
        int u,v;
        cin>>u>>v;
        t[u].push_back(v);
        t[v].push_back(u);
    }
    int target = ((sz(t[1])==2)?1:-1);
    vector<int>leaf;
    for(int i = 2; i<=n; i++){
        if(sz(t[i])==1)
            leaf.push_back(i);
        if(sz(t[i])==3)
            target = i;
    }
    if(sz(leaf)>2){
        cout<<0<<endl;
        return;
    }
    if(sz(leaf)==1){
        cout<<expo(2,n,mod)<<endl;
        return;
    }
    vector<int>parent(n+1);
    dfs(1,-1,parent);
    int leaf1 = leaf[0], leaf2 = leaf[1];
    int x = n;
    while(leaf1!=target and leaf2!=target){
        x-=2;
        leaf1 = parent[leaf1];
        leaf2 = parent[leaf2];
    }
    if(leaf1==target and leaf2==target){
        cout<<expo(2,x+1,mod)<<endl;
    }else{
        cout<<(expo(2,x,mod) + expo(2,x-1,mod))%mod<<endl;
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