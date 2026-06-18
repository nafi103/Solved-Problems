#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
#define mod 998244353
#define inf 1e15+10
#define pb push_back
#define ff first
#define ss second
#define sz(x) (int)(x).size()
#define set_bits(x) __builtin_popcount(x)
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


int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int n,m,q;
    cin>>n>>m>>q;
    vector<vector<int>>distance(n+1,vector<int>(n+1,inf));
    while(m--){
        int u,v,w;
        cin>>u>>v>>w;
        distance[u][v] = min(distance[u][v],w);
        distance[v][u] = min(distance[v][u],w);
    }
    for(int i = 1; i<=n; i++) distance[i][i] = 0;
    for(int k = 1; k<=n; k++){
        for(int i = 1; i<=n; i++){
            for(int j = i+1; j<=n; j++){
                distance[i][j] = min(distance[i][j], distance[i][k]+distance[j][k]);
                distance[j][i] = distance[i][j];
            }
        }
    }
    while(q--){
        int u,v;
        cin>>u>>v;
        cout<<(distance[u][v]==inf?-1: distance[u][v])<<endl;
    }
}