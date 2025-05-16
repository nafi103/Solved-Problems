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
    int n,ans = 0;
    cin>>n;
    vector<pair<int,int>>point(n);
    for(auto &[f,s]: point)
        cin>>f>>s;
    using pii = pair<int,int>;
    vector<pair<int,int>>have;
    vector<vector<pii>>slope(n,vector<pii>(n));
    for(int i = 0; i<n; i++){
        for(int j = i+1; j<n; j++){
            int nom = point[j].ss-point[i].ss, denom = point[j].ff - point[i].ff;
            int g = gcd(nom,denom);
            nom/=g;
            denom/=g;
            if(denom<0){
                nom*=-1;
                denom*=-1;
            }
            slope[i][j] = {nom,denom};
            slope[j][i] = {nom,denom};
        }
    }
    have.reserve((1<<n));
    for(int mask = 1; mask<(1<<n); mask++){
        if(__builtin_popcountll(mask)==1)
            continue;
        bool flag = true;
        int l = 0, r = 0;
        for(int i = 0; i<n; i++){
            if((1<<i)&mask){
                l = i;
                break;
            }
        }
        for(int i = l+1; i<n; i++){
            if((1<<i)&mask){
                r = i;
                break;
            }
        }
        pii curr_slope = slope[l][r];
        for(int i = r+1; i<n; i++){
            if((1<<i)&mask){
                if(slope[i][l]!=curr_slope){
                    flag = false;
                    break;
                }
            }
        }
        if(flag){
            have.push_back({__builtin_popcountll(mask),mask});
        }
    }
    sort(all(have),[&](pii &a, pii &b){
        if(a.ff!=b.ff)
            return a.ff<b.ff;
        return a.ss>b.ss;
    });
    int taken = 0;
    while(!have.empty()){
        auto [x,mask] = have.back();
        have.pop_back();
        if((mask^taken)==mask+taken){
            taken^=mask;
            ans++;
        }
    }
    if(taken!=(1<<n)-1)
        ans++;
    cout<<ans<<endl;
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