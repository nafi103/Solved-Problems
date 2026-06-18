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
    int n,m;
    string str;
    cin>>n>>m>>str;
    vector<vector<int>>grid(n,vector<int>(m));
    for(int i = 0; i<n; i++){
        for(int j = 0; j<m; j++){
            cin>>grid[i][j];
        }
    }
    int r = 0, c = 0;
    for(int pos = 0; pos<sz(str); pos++){
        int sum = 0;
        if(str[pos]=='D'){
            for(int j = 0; j<m; j++){
                sum+=grid[r][j];
            }
        }else{
            for(int i = 0; i<n; i++){
                sum+=grid[i][c];
            }
        }
        grid[r][c] = -sum;
        if(str[pos]=='D') r++;
        else c++;
    }
    for(int j = 0; j<m-1; j++){
        grid[n-1][m-1]+=(-grid[n-1][j]);
    }
    for(int i = 0; i<n; i++){
        for(int j = 0; j<m; j++){
            cout<<grid[i][j]<<" ";
        }
        cout<<endl;
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