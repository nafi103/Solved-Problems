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
map<pair<int,int>, int> dp;
int n;
vector<int> wt,power_of_two(31),pref;

int f(int pos, int rem){
    if(rem<0)
        return 0;
    if(pos==n)
        return 1;
    if(pref[n]-pref[pos]<=rem){
        return power_of_two[n-pos];
    }
    if(dp.count({pos,rem}))
        return dp[{pos,rem}];
    return dp[{pos,rem}] = f(pos+1,rem-wt[pos]) + f(pos+1,rem);
}

void solve()
{
    pref.clear();
    wt.clear();
    dp.clear();
    int w;
    cin>>n>>w;
    wt.resize(n);
    pref.resize(n+1);
    readv(wt);
    sort(rbegin(wt),rend(wt));
    pref[0] = 0;
    for(int i = 0; i<n; i++){
        pref[i+1] = pref[i] + wt[i];
    }
    cout<<f(0,w)<<endl;
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
    power_of_two[0] = 1;
    for(int i = 1; i<31; i++)
        power_of_two[i] = power_of_two[i-1]*2;
    for(int z = 1; z<=t; z++){
        cout<<"Case "<<z<<": ";
        solve();
    }
}