#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

#define pi acos(-1.0)
const int mod = 998244353;
#define inf 1e18+10
#define pb push_back
#define x first
#define y second
#define sz(x) (int)(x).size()
#define set_bits(x) __builtin_popcountll(x)
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

int max_mask,n;
const int dummy = 20;
vector<int>dp;
vector<pair<int,int>>point;

pair<int,int> calc_slope(pair<int,int> &a, pair<int,int>&b){
    if(a.y==b.y){
        return {1,0};
    }
    if(a.x==b.x){
        return {0,1};
    }
    int dy = a.y-b.y, dx = a.x-b.x;
    int g = gcd(abs(dy),abs(dx));
    dy/=g;
    dx/=g;
    if(dx<0){
        dy*=-1;
        dx*=-1;
    }
    return {dy,dx};
}

int f(int mask){
    if(mask==max_mask){
        return 0;
    }
    if(set_bits(mask)==n-1){
        return 1;
    }
    int &ans = dp[mask];
    if(ans!=dummy)
        return ans;
    int i = 0;
    while((1ll<<i)&mask){
        i++;
    }
    for(int j = i+1; j<n; j++){
        if(((1ll<<j)&mask)==0){
            int new_mask = ((mask|(1ll<<i))|(1ll<<j));
            pair<int,int> slope = calc_slope(point[i],point[j]);
            for(int k = j+1; k<n; k++){
                if(!((1ll<<k)&mask)){
                    pair<int,int> another_slope = calc_slope(point[i],point[k]);
                    if(another_slope==slope){
                        new_mask|=(1ll<<k);
                    }
                }
            }
            ans = min(ans,1+f(new_mask));
        }
    }
    return ans;
}


void solve()
{
    dp.clear();
    point.clear();
    int ans = 0;
    cin>>n;
    point.resize(n);
    for(auto &[f,s]: point)
        cin>>f>>s;
    max_mask = (1ll<<n) - 1;
    dp.assign(max_mask+1,dummy);
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