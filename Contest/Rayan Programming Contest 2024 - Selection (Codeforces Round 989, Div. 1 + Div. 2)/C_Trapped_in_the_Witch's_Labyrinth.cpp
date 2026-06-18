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


void solve()
{
    int n, m;
    cin >> n >> m;
    string c[n+1];
    for(int i = 1 ; i <= n ; i++) cin >> c[i] , c[i] = "-" + c[i];
    vector<pair<int,int>> jda[n+2][m+2];
    for(int i = 1 ; i <= n ; i++){
        for(int j = 1 ; j <= m ; j++){
            if(c[i][j] == 'U') jda[i-1][j].push_back({i , j});
            if(c[i][j] == 'R') jda[i][j+1].push_back({i , j});
            if(c[i][j] == 'D') jda[i+1][j].push_back({i , j});
            if(c[i][j] == 'L') jda[i][j-1].push_back({i , j});
        }
    }
    int vis[n+2][m+2] = {};
    queue<pair<int,int>> q;
    for(int j = 0 ; j <= m+1 ; j++) vis[0][j] = 1 , q.push({0 , j});
    for(int i = 1 ; i <= n+1 ; i++) vis[i][0] = 1 , q.push({i , 0});
    for(int j = 1 ; j <= m+1 ; j++) vis[n+1][j] = 1 , q.push({n+1 , j});
    for(int i = 1 ; i <= n ; i++) vis[i][m+1] = 1 , q.push({i , m+1});
    while(q.size()){
        auto [i , j] = q.front();
        q.pop();
        for(auto [a , b] : jda[i][j]){
            if(vis[a][b] == 0){
                vis[a][b] = 1;
                q.push({a , b});
            }
        }
    }
    for(int i = 1 ; i <= n ; i++){
        for(int j = 1 ; j <= m ; j++){
            if(c[i][j] == '?' and
            vis[i-1][j] and vis[i][j+1] and vis[i+1][j] and vis[i][j-1]) vis[i][j] = 1;
        }
    }
    int ans = n * m;
    for(int i = 1 ; i <= n ; i++){
        for(int j = 1 ; j <= m ; j++){
            if(vis[i][j] == 1) ans -= 1;
        }
    }
    cout << ans << endl;
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