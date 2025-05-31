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
int n,final_mask;
vector<int>health,dp;
vector<vector<int>>damage;

int f(int mask){
    if(mask==final_mask)
        return 0;
    int &ans = dp[mask];
    if(ans!=inf){
        return ans;
    }
    vector<int>max_damage(n,1);
    for(int i = 0; i<n; i++){
        if(mask&(1<<i)){
            for(int j = 0; j<n; j++){
                max_damage[j] = max(max_damage[j],damage[i][j]);
            }
        }
    }
    for(int i = 0; i<n; i++){
        if((mask&(1<<i))==0){
            ans = min(ans, (health[i]+max_damage[i]-1)/max_damage[i] + f(mask|(1<<i)));
        }
    }
    return ans;
}

void solve()
{
    dp.clear();
    health.clear();
    damage.clear();
    cin>>n;
    final_mask = (1<<n) - 1;
    dp.assign(final_mask+1,inf);
    health.resize(n);
    damage.resize(n,vector<int>(n));
    readv(health);
    for(int i = 0; i<n; i++){
        for(int j = 0; j<n; j++){
            char c;
            cin>>c;
            damage[i][j] = c-'0';
        }
    }
    cout<<f(0)<<endl;
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
        cout<<"Case "<<z<<": ";
        solve();
    }
}