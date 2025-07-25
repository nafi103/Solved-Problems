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

const int mx = 17;
vector<vector<int>>t,parents(17,vector<int>(100010));
vector<int>value(100010);

void dfs(int node, int parent){
    parents[0][node] = parent;
    for(auto &x: t[node]){
        if(x!=parent) dfs(x,node);
    }
}

void ini(int n){
    int p = log2(n) + 1,u;
    for(int i = 0; i<mx; i++){
        for(int j = 0; j<n; j++)
            parents[i][j] = -1;
    }
    t.clear();
    t.resize(n);
    for(int v = 1; v<n; v++){
        cin>>u>>value[v];
        t[u].push_back(v);
        t[v].push_back(u);
    }
}


void solve()
{
    int n,q;
    cin>>n>>q;
    ini(n);
    dfs(0,-1);
    int p = log2(n) + 1;
    for(int i = 1; i<p; i++){
        for(int j = 0; j<n; j++){
            int par = parents[i-1][j];
            if(par!=-1)
                parents[i][j] = parents[i-1][par];
        }
    }
    while(q--){
        int node, val;
        cin>>node>>val;
        for(int i = p-1; i>=0; i--){
            if(parents[i][node]!=-1 and value[parents[i][node]]>=val)
                node = parents[i][node];
        }
        cout<<node<<endl;
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
    value[0] = 1;
    for(int z = 1; z<=t; z++){
        cout<<"Case "<<z<<":\n";
        solve();
    }
}