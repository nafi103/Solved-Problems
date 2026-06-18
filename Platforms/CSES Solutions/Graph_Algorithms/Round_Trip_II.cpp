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
#define inf 1e18+10
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
template <class T> using pbds = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update >;
 
#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif
 
/****************************************************************/
vector<vector<int>>g;
vector<int>parent;
vector<bool>in_path;
int s = -1, e = -1;

void dfs(int node, int par){
    if(s!=-1 or e!=-1) return;
    parent[node] = par;
    in_path[node] = true;
    for(auto &child : g[node]){
        if(s!=-1 or e!=-1) return;
        if(!in_path[child] and parent[child]==-1){
            dfs(child,node);
        }else if(in_path[child]){
            s = node;
            e = child;
            return;
        }
    }
    in_path[node] = false;
}

void solve()
{
    int n,m,u,v;
    cin>>n>>m;
    g.resize(n+1);
    parent.assign(n+1,-1);
    in_path.assign(n+1,false);
    for(int i = 1; i<=m; i++){
        cin>>u>>v;
        g[u].pb(v);
    }
    for(int i = 1; i<=n; i++){
        if(s!=-1) break;
        if(parent[i]==-1){
            dfs(i,-1);
        }
    }
    if(s==-1){
        cout<<"IMPOSSIBLE"<<endl;
        return;
    }
    vector<int>ans;
    debug(s) debug(e)
    debug(parent)
    while(s!=e){
        ans.pb(s);
        s = parent[s];
    }
    ans.pb(s);
    reverse(all(ans));
    ans.pb(s);
    cout<<sz(ans)<<endl;
    writev(ans);
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