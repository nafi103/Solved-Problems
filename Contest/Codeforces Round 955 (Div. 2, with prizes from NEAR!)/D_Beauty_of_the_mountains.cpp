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
    int n,m,k;
    cin>>n>>m>>k;
    vector<vector<int>>grid(n+1,vector<int>(m+1)),pahar(n+1,vector<int>(m+1));
    for(int i = 1; i<=n; i++){
        for(int j = 1; j<=m; j++){
            cin>>grid[i][j];
        }
    }
    debug(grid)
    int shundor = 0, bisri = 0, shundor_height = 0, bisri_height = 0;
    for(int i = 1; i<=n; i++){
        for(int j = 1; j<=m; j++){
            char x;
            cin>>x;
            pahar[i][j] = (x=='1');
            if(pahar[i][j]){
                shundor++;
                shundor_height+=grid[i][j];
            }
            else{
                bisri++;
                bisri_height+=grid[i][j];
            }
            pahar[i][j]+=pahar[i-1][j];
            pahar[i][j]+=pahar[i][j-1];
            pahar[i][j]-=pahar[i-1][j-1];
        }
    }
    if(shundor_height==bisri_height){
        yes;
        return;
    }
    int g = 0;
    for(int i = 1; i<=n-k+1; i++){
        for(int j = 1; j<=m-k+1; j++){
            int p = i+k-1, q = j+k-1;
            int grid_e_shundor_pahar = pahar[p][q] - pahar[i-1][q] - pahar[p][j-1] + pahar[i-1][j-1];
            int grid_e_bisri_pahar = (k*k) - grid_e_shundor_pahar;
            debug(grid_e_shundor_pahar) debug(grid_e_bisri_pahar)
            g = gcd(g,abs(grid_e_bisri_pahar-grid_e_shundor_pahar));
        }
    }
    if(g==0){
        no;
        return;
    }
    if(abs(shundor_height-bisri_height) % g == 0){
        yes;
    }else{
        no;
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
    for(int z = 1; z<=t; z++){
        // google(z);
        solve();
    }
}