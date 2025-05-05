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
bool possible = true;
vector<int>color;
vector<vector<int>>g;

void dfs(int node, int c){
    if(!possible) return;
    color[node] = c;
    for(auto &x: g[node]){
        if(color[x]==-1){
            dfs(x,c^1);
        }else if(color[x]==color[node]){
            possible = false;
            return;
        }
    }
}

void solve()
{
    int n,m,u,v;
    cin>>n>>m;
    g.resize(n+1);
    color.resize(n+1,-1);
    while(m--){
        cin>>u>>v;
        g[u].pb(v);
        g[v].pb(u);
    }
    for(int node = 1; node<=n; node++){
        if(color[node]==-1){
            dfs(node,0);
            if(!possible){
                cout<<"IMPOSSIBLE"<<endl;
                return;
            }
        }
    }
    for(int i = 1; i<=n; i++){
        cout<<color[i]+1<<" ";
    }
    cout<<endl;
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