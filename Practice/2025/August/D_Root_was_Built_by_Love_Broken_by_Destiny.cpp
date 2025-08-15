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
const int N = 200005;
vector<int>color,leaf,fact(N);
vector<vector<int>>g;

bool bipartite(int node, int col){
    color[node] = col;
    bool flag = true;
    int not_leaf = 0;
    for(auto &x: g[node]){
        if(color[x]==-1){
            flag&=bipartite(x,col^1);
        }else if(color[x]==col){
            flag = false;
        }
        if(sz(g[x])==1)
            leaf[node]++;
        else
            not_leaf++;
    }
    return flag and not_leaf<=2;
}

void solve()
{
    leaf.clear();
    color.clear();
    g.clear();
    int n,m,src = 0;
    cin>>n>>m;
    leaf.assign(n,0);
    color.assign(n,-1);
    g.resize(n);
    for(int i = 0; i<m; i++){
        int u,v;
        cin>>u>>v;
        u--,v--;
        g[u].push_back(v);
        g[v].push_back(u);
    }
    int not_leaf = 0;
    for(int i = 0; i<n; i++){
        if(sz(g[i])==1){
            src = i;
        }else{
            not_leaf++;
        }
    }
    if(m>n-1 or !bipartite(src,0)){
        cout<<0<<endl;
        return;
    }
    int ans = 2 * (not_leaf>1?2:1);
    for(auto &x: leaf){
        ans = (ans*fact[x])%mod;
    }
    cout<<ans<<endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    fact[0] = 1;
    for(int i = 1; i<N; i++){
        fact[i] = (fact[i-1]*i)%mod;
    }
    int t = 1;
    cin >> t;
    for(int z = 1; z<=t; z++){
        // cout<<"Case "<<z<<": ";
        solve();
    }
}