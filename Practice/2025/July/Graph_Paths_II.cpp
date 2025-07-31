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
#define inf 2e18+10
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

vector<vector<int>> multiply(vector<vector<int>>&a, vector<vector<int>>&b){
    int n = sz(a);
    vector<vector<int>>result(n,vector<int>(n,inf));
    for(int i = 0; i<n; i++){
        for(int j = 0; j<n; j++){
            for(int k = 0; k<n; k++){
                result[i][j]=min(result[i][j],a[i][k]+b[k][j]);
            }
        }
    }
    return result;
}


vector<vector<int>> expo(vector<vector<int>>t, int p){
    int n = sz(t);
    vector<vector<int>>result(n,vector<int>(n,inf));
    for(int i = 0; i<n; i++)
        result[i][i] = 0;
    while(p>0){
        if(p&1)
            result = multiply(result,t);
        t = multiply(t,t);
        p>>=1;
    }
    return result;
}

void solve()
{
    int n,m,k;
    cin>>n>>m>>k;
    vector<vector<int>>g(n,vector<int>(n,inf));
    while(m--){
        int u,v,w;
        cin>>u>>v>>w;
        u--,v--;
        g[u][v] = min(g[u][v],w);
    }
    g = expo(g,k);
    if(g[0][n-1]==inf)
        cout<<-1<<endl;
    else
        cout<<g[0][n-1]<<endl;
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