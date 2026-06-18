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
vector<int>mt;
vector<bool>visited;

bool try_kuhn(int v){
    if(visited[v])
        return false;
    visited[v] = true;
    for(auto &to: g[v]){
        if(mt[to]==-1 or try_kuhn(mt[to])){
            mt[to] = v;
            return true;
        }
    }
    return false;
}

void solve()
{
    int n,m,k,ans = 0;
    cin>>n>>m>>k;
    mt.assign(m,-1);
    g.resize(n);
    while(k--){
        int u,v;
        cin>>u>>v;
        u--,v--;
        g[u].push_back(v);
    }
    for(int i = 0; i<n; i++){
        visited.assign(n,false);
        if(try_kuhn(i))
            ans++;
    }
    cout<<ans<<endl;
    for(int i = 0; i<m; i++){
        if(mt[i]!=-1){
            cout<<mt[i]+1<<" "<<i+1<<endl;
        }
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
    for(int z = 1; z<=t; z++){
        // cout<<"Case "<<z<<": ";
        solve();
    }
}