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

vector<int> value, parent, sum, color;
vector<vector<pair<int,int>>>g;
vector<map<int,int>> child_col_sum;

void dfs(int node, int par, int val){
    value[node] = val;
    parent[node] = par;
    for(auto [child,w]: g[node]){
        if(child!=par){
            sum[node]+=w;
            child_col_sum[node][color[child]]+=w;
            dfs(child,node,w);
        }
    }
}

void reset(int n);

void solve()
{
    int n,q;
    cin>>n>>q;
    reset(n);
    for(int i = 1; i<=n; i++)
        cin>>color[i];
    for(int i = 1; i<n; i++){
        int u,v,w;
        cin>>u>>v>>w;
        g[u].push_back({v,w});
        g[v].push_back({u,w});
    }
    dfs(1,-1,0);
    int ans = 0;
    for(int i = 1; i<=n; i++){
        ans+=(sum[i] - child_col_sum[i][color[i]]);
    }
    while(q--){
        int node, new_col;
        cin>>node>>new_col;
        int prev_col = color[node];
        if(prev_col!=new_col){
            int par = parent[node];
            if(par!=-1){
                child_col_sum[par][prev_col]-=value[node];
                child_col_sum[par][new_col]+=value[node];
                if(prev_col==color[par])
                    ans+=value[node];
                else if(prev_col!=color[par] and new_col==color[par])
                    ans-=value[node];
            }
            ans-=(sum[node]-child_col_sum[node][prev_col]);
            ans+=(sum[node]-child_col_sum[node][new_col]);
        }
        color[node] = new_col;
        cout<<ans<<endl;
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

void reset(int n){
    value.clear();
    parent.clear();
    sum.clear();
    color.clear();
    g.clear();
    child_col_sum.clear();
    value.resize(n+1);
    parent.resize(n+1);
    sum.resize(n+1);
    color.resize(n+1);
    g.resize(n+1);
    child_col_sum.resize(n+1);
}