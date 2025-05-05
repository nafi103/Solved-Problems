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
vector<int>color;
bool flag = true;

void dfs(int node, int col){
    color[node] = col;
    for(auto &nbr: g[node]){
        if(color[nbr]==-1){
            dfs(nbr,col^1);
        }else if(color[node]==color[nbr]){
            flag = false;
        }
    }
}


void solve()
{
    g.clear();
    color.clear();
    flag = true;
    int n,u,v;
    cin>>n;
    g.resize(n+1);
    color.assign(n+1,-1);
    vector<int>cnt(n+1,0);
    for(int i = 0; i<n; i++){
        cin>>u>>v;
        cnt[u]++;
        cnt[v]++;
        if(cnt[u]>2 or cnt[v]>2){
            flag = false;
        }
        g[u].pb(v);
        g[v].pb(u);
    }
    if(!flag){
        no;
        return;
    }
    for(int i = 1; i<=n; i++){
        if(color[i]==-1){
            dfs(i,0);
        }
    }
    if(flag) yes;
    else no;
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