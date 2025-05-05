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
#define yes cout<<"Yes"<<endl
#define no cout<<"No"<<endl
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
    int n;
    cin>>n;
    vector<int>cnt(n+1,0);
    for(int i = 0; i<n; i++){
        int x;
        cin>>x;
        cnt[x]++;
    }
    int extra = 0;
    for(int i = 1; i<=n; i++){
        if(cnt[i]==0){
            if(extra==1){
                no;
                return;
            }
            if(extra>=2){
                extra-=2;
                cnt[i]+=2;
            }
            continue;
        }
        if(cnt[i]&1){
            if(cnt[i]==1 and extra==0){
                no;
                return;
            }
            if(extra){
                extra--;
                cnt[i]++;
            }else{
                cnt[i]--;
                extra++;
            }
        }
        if(cnt[i]>=2){
            extra+=cnt[i]-2;
            cnt[i] = 2;
        }
    }
    yes;
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