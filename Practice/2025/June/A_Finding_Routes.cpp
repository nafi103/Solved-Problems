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
vector<vector<int>>g;
map<string,int>mp;
map<int,string>rmp;

void dfs(int node){
    cout<<rmp[node]<<endl;
    if(!g[node].empty())
        dfs(g[node][0]);
}

void solve()
{
    g.clear();
    mp.clear();
    rmp.clear();
    int n;
    cin>>n;
    g.resize(n);
    vector<int>in_degree(n,0);
    for(int i = 1; i<n; i++){
        string u,v;
        cin>>u>>v;
        if(mp.count(u)==0){
            rmp[sz(mp)] = u;
            mp[u] = sz(mp);
        }
        if(mp.count(v)==0){
            rmp[sz(mp)] = v;
            mp[v] = sz(mp);
        }
        int iu = mp[u],iv = mp[v];
        in_degree[iv]++;
        g[iu].push_back(iv);
    }
    int src = 0;
    for(int i = 0; i<n; i++){
        if(in_degree[i]==0){
            src = i;
            break;
        }
    }
    dfs(src);
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
    cin >> t;
    for(int z = 1; z<=t; z++){
        cout<<"Case "<<z<<":\n";
        solve();
    }
}