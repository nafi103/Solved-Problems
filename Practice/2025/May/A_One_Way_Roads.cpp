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
map<pair<int,int>,int>cost;
vector<vector<int>>g;

int dfs(int node, int child){
    int curr_cost = 0;
    if(cost.count({node,child}) == 0)
        curr_cost = cost[{child,node}];
    if(child==1){
        return curr_cost;
    }
    for(auto &grandchild: g[child]){
        if(grandchild!=node){
            return curr_cost+dfs(child,grandchild);
        }
    }
}


void solve()
{
    cost.clear();
    g.clear();
    int n;
    cin>>n;
    g.resize(n+1);
    for(int i = 0; i<n; i++){
        int u,v,w;
        cin>>u>>v>>w;
        g[u].push_back(v);
        g[v].push_back(u);
        cost[{u,v}] = w;
    }
    cout<<min(dfs(1,g[1][0]),dfs(1,g[1][1]))<<endl;
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
        cout<<"Case "<<z<<": ";
        solve();
    }
}