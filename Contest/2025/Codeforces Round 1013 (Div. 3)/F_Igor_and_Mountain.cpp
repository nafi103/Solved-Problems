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
    int n,m,d;
    cin>>n>>m>>d;
    vector<vector<int>>grid(n+1,vector<int>(m+2,0));
    for(int i = 1; i<=n; i++){
        for(int j = 1; j<=m; j++){
            char c;
            cin>>c;
            if(c=='X')
                grid[i][j] = 1;
        }
    }
    int len =  sqrt(d*d + 1);

    vector<int>last = grid[n], calc(m+2,0);
    for(int j = 1; j<=m; j++){
        int left = max(0ll,j-d), right = min(m,j+d);
        calc[left]+=last[j];
        calc[right+1]-=last[j];
    }
    for(int j = 1; j<=m; j++){
        calc[j]+=calc[j-1];
    }
    for(int j = 0; j<=m+1; j++){
        if(last[j]==0)
            calc[j] = 0;
    }
    grid[n] = calc;
    for(int i = n-1; i>=1; i--){
        vector<int>prev = grid[i+1],curr(m+2,0);
        calc.assign(m+2,0);
        for(int j = 1; j<=m; j++){
            if(prev[j]){
                int left = max(0ll,j-(d-1)), right = min(m+1,j+d);
                curr[left]+=prev[j];
                curr[left] = ((curr[left]%mod)+mod)%mod;
                curr[right]-=prev[j];
                curr[right] = ((curr[right]%mod)+mod)%mod;
            }
        }
        for(int j = 1; j<=m+1; j++){
            curr[j]+=curr[j-1];
            curr[j] = ((curr[j]%mod)+mod)%mod;
        }
        for(int j = 0; j<m+2; j++){
            if(grid[i][j]==0)
                curr[j] = 0;
        }
        debug(curr)
        for(int j = 1; j<=m; j++){
            if(curr[j]){
                int left = max(0ll,j-d), right = min(m+1,j+d+1);
                debug(left) debug(right)
                calc[left]+=curr[j];
                calc[left] = ((calc[left]%mod)+mod)%mod;
                calc[right]-=curr[j];
                calc[right] = ((calc[right]%mod)+mod)%mod;
            }
        }
        for(int j = 1; j<=m; j++){
            calc[j]+=calc[j-1];
            calc[j] = ((calc[j]%mod)+mod)%mod;
        }
        for(int j = 0; j<=m+1; j++){
            if(grid[i][j]==0)
                calc[j] = 0;
        }
        grid[i] = calc;
    }
    debug(grid)
    cout<<accumulate(all(grid[1]),0ll)%mod<<endl;
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