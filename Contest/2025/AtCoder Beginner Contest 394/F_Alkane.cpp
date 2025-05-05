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
#define pb push_back
#define ff first
#define ss second
#define sz(x) (int)(x).size()
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
template <class T> using pbds = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update >;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/
int n;
vector<vector<int>>t;
vector<bool>alcane;
vector<int>dp;

void dfs(int node, int parent){
    if(sz(t[node])==1 or sz(t[node])==4){
        alcane[node] = true;
    }
    for(auto &x: t[node]){
        if(x!=parent){
            dfs(x,node);
        }
    }
}

void dfs2(int node, int parent){
    for(auto &x: t[node]){
        if(x!=parent){
            dfs2(x,node);
            if(alcane[node]) dp[node]+=dp[x];
        }
    }
}


void solve()
{
    cin>>n;
    t.resize(n+1);
    alcane.assign(n+1,false);
    dp.resize(n+1,1);
    for(int i = 1; i<n; i++){
        int u,v;
        cin>>u>>v;
        t[u].pb(v);
        t[v].pb(u);
    }
    int src = 1;
    for(int i = 1; i<=n; i++){
        if(sz(t[i])==1){
            src = i;
            break;
        }
    }
    dfs(src,-1);
    dfs2(src,-1);
    int ans = *max_element(all(dp));
    cout<<(ans<=5?-1:ans)<<endl;
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
        // google(z);
        solve();
    }
}