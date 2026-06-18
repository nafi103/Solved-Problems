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
int expo(int a, int b, int m) {int res = 1; while (b > 0) {if (b & 1)res = (res * a) % m; a = (a * a) % m; b = b >> 1;} return res;}

vector<bool>visited;

void dfs(int v, vector<vector<int>> const& g, vector<int>& output) {
    visited[v] = true;
    for (auto u : g[v])
        if (!visited[u])
            dfs(u, g, output);
    output.push_back(v);
}

void strongly_connected_components(vector<vector<int>> const& g,
                                vector<int>& components) {
    int n = sz(g);
    components.clear();

    vector<int> order;
    visited.assign(n, false);

    for (int i = 0; i < n; ++i)
        if (!visited[i])
            dfs(i, g, order);

    vector<vector<int>> g_rev(n);
    for (int v = 0; v < n; ++v)
        for (int u : g[v])
            g_rev[u].push_back(v);

    visited.assign(n, false);
    reverse(order.begin(), order.end());
    int component_id = 0;

    for (int v : order) {
        if (!visited[v]) {
            vector<int> component;
            dfs(v, g_rev, component);
            components.push_back(component.size());
            component_id++;
        }
    }
}

void solve()
{
    int n;
    cin>>n;
    vector<vector<int>>g(n+1);
    vector<int>components;
    for(int i = 1; i<=n; i++){
        int x;
        cin>>x;
        g[i].push_back(x);
    }
   strongly_connected_components(g,components);
   vector<int>spf(n+1);
   iota(all(spf),0);
   for(int i = 2; i*i<=n; i++){
        if(spf[i]==i){
            for(int j = i+i; j<=n; j+=i)
                spf[j] = min(spf[j],i);
        }
   }
   vector<int> max_pow(n+1,0);
   for(auto x: components){
        while(x>1){
            int curr = spf[x],cnt = 0;
            while(spf[x]==curr){
                cnt++;
                x/=curr;
            }
            max_pow[curr] = max(max_pow[curr],cnt);
        }
   }
   int ans = 1;
   for(int i = 1; i<=n; i++){
        if(max_pow[i]==0)
            continue;
        ans = (ans * expo(i,max_pow[i],mod))%mod;
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
    int t = 1;
    for(int z = 1; z<=t; z++){
        // cout<<"Case "<<z<<": ";
        solve();
    }
}