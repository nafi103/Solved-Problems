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
int n;
vector<vector<int>>nCr(11);
vector<int>pref(11), num,power_of_nine(11),power_of_ten(11);
vector<vector<pair<int,int>>>dp;
const pair<int,int> dummy = {-1,-1};

void make_vector(int x){
    num.clear();
    while(x){
        num.push_back(x%10);
        x/=10;
    }
    reverse(all(num));
    n = sz(num);
}

int calc(){
    int mult = 0;
    for(int i = 1; i<=n-2; i++){
        mult+=pref[i];
    }
    return mult*9 + 1; // 1 for 0
}

pair<int,int> f(int pos, int same){
    if(pos==n)
        return {0,1};
    if(!same){
        return {pref[n-pos],power_of_ten[n-pos]};
    }
    if(dp[pos][same]!=dummy)
        return dp[pos][same];
    int l = (pos==0) ? 1:0;
    int r = num[pos];
    auto &[zeros,numbers] = dp[pos][same];
    zeros = 0, numbers = 0;
    for(int i = l; i<=r; i++){
        auto [next_zero, next_num] = f(pos+1, i==r);
        zeros+=next_zero;
        if(i==0)
            zeros+=next_num;
        numbers+=next_num;
    }
    return dp[pos][same];
}

void solve()
{
    int l,r;
    cin>>l>>r;
    dp.clear();
    make_vector(r);
    dp.resize(n,vector<pair<int,int>>(2,dummy));
    int add = calc();
    debug(add)
    auto [r_zero, dum] = f(0,1);
    r_zero+=add;
    if(l==0){
        cout<<r_zero<<endl;
        return;
    }
    debug(r_zero)
    l--;
    dp.clear();
    make_vector(l);
    dp.resize(n,vector<pair<int,int>>(2,dummy));
    add = calc();
    auto [l_zero, dumdum] = f(0,1);
    l_zero+=add;
    debug(l_zero)
    cout<<r_zero - l_zero<<endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    power_of_ten[0] = power_of_nine[0] = 1;
    for(int i = 1; i<11; i++){
        power_of_ten[i] = power_of_ten[i-1]*10;
        power_of_nine[i] = power_of_nine[i-1]*9;
    }
    for(int i = 0; i<11; i++){
        nCr[i].resize(i+1);
        nCr[i][0] = nCr[i][i] = 1;
        for(int j = 1; j<i; j++){
            nCr[i][j] = nCr[i-1][j] + nCr[i-1][j-1];
        }
    }
    pref[0] = 0;
    for(int i = 1; i<11; i++){
        pref[i] = 0;
        for(int j = 1; j<=i; j++){
            pref[i] += nCr[i][j] * power_of_nine[i-j] * j;
        }
    }
    debug(pref)
    int t = 1;
    cin >> t;
    for(int z = 1; z<=t; z++){
        cout<<"Case "<<z<<": ";
        solve();
    }
}