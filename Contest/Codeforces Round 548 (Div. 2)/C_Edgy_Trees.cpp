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

using pii = pair<int,int>;
vector<vector<pii>>t;
vector<bool>visited;
int n,k;

int dfs(int node){
    visited[node] = true;
    int cnt = 1;
    for(auto &[nbr,col]: t[node]){
        if(!visited[nbr] and !col){
            cnt+=dfs(nbr);
        }
    }
    return cnt;
}


void solve()
{
    int neg = 0;
    cin>>n>>k;
    t.resize(n+1);
    visited.assign(n+1,false);
    for(int i = 1; i<n; i++){
        int u,v,col;
        cin>>u>>v>>col;
        t[u].pb({v,col});
        t[v].pb({u,col});
    }
    for(int i = 1; i<=n; i++){
        if(!visited[i]){
            int cnt = dfs(i);
            neg = (neg+expo(cnt,k,mod))%mod;
        }
    }
    int pos = expo(n,k,mod);
    cout<<(pos-neg+mod)%mod<<endl;
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