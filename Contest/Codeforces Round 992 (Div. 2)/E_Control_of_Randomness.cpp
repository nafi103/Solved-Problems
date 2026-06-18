#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
#define mod 998244353
#define inf 1e17+10
#define pb push_back
#define ff first
#define ss second
#define sz(x) (int)(x).size()
#define set_bits(x) __builtin_popcount(x)
#define LSOne(x) ((x)&(-x))
#define all(x) x.begin(), x.end()
#define readv(v)      \
    for (auto &x : v) \
    cin >> x
#define writev(v)     \
    for (auto &x : v) \
    cout << x << " "; \
    cout<<endl
#define endl "\n"
#define yes cout<<"YES"<<endl
#define no cout<<"NO"<<endl
#define remove_punctuation(text) regex_replace(text, regex(R"([^\w\s])"), "")
#define fastIO ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr)
template <class T> using pbds = tree<T, null_type, less_equal<T>, rb_tree_tag, tree_order_statistics_node_update >;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/
//dp[i][j] = expected number of steps to reach 1 from node i using j coins
vector<vector<int>>dp,t; 
vector<int>parent;

int f(int node, int coin){
    if(coin<0) return inf;
    if(node==-1) return -1;
    if(node==1) return 0;
    if(dp[node][coin]!=-1) return dp[node][coin];
    int &ans = dp[node][coin];
    int adj_nodes = sz(t[node]), reach = parent[parent[node]];
    ans = min(2+f(reach,coin-1), f(reach,coin)+2*adj_nodes);
    ans = ((ans%mod)+mod)%mod;
    return ans;
}

void dfs(int node, int par){
    parent[node] = par;
    for(auto &x: t[node]){
        if(x!=par) dfs(x,node);
    }
}

void clearAll(){
    t.clear();
    dp.clear();
    parent.clear();
}

void init(int n){
    t.resize(n+1);
    dp.assign(n+1,vector<int>(n+1,-1));
    parent.assign(n+1,-1);
}

void solve()
{
    int n,q;
    cin>>n>>q;
    init(n);
    for(int i = 1; i<n; i++){
        int u,v;
        cin>>u>>v;
        t[u].pb(v);
        t[v].pb(u);
    }
    dfs(1,-1);
    while(q--){
        int node, coin;
        cin>>node>>coin;
        cout<<1+f(parent[node],min(n,coin))<<endl;
    }
    clearAll();
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
        // google(z);
        solve();
    }
}