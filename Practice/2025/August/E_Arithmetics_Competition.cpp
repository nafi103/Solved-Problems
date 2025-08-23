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
#define sz(x) (int)(x).size()
#define LSOne(x) ((x)&(-x))
#define all(x) x.begin(), x.end()
#define readv(v)      \
    for (auto &x : v) \
    cin >> x
#define endl "\n"
#define fastIO ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr)
template <class T> using pbds = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update >;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

void calculate_prefix_sum(vector<int> &pref,vector<int>&v,int &n){
    pref.resize(n+1);
    pref[0] = 0;
    for(int i = 1; i<=n; i++){
        pref[i] = pref[i-1]+v[i-1];
    }
}

void solve()
{
    int n,m,q;
    cin>>n>>m>>q;
    vector<int>a(n),b(m);
    readv(a);readv(b);
    sort(all(a),greater<int>());
    sort(all(b),greater<int>());
    vector<int>prefa(n+1),prefb(m+1),total_pref(n+m+1);
    calculate_prefix_sum(prefa,a,n);
    calculate_prefix_sum(prefb,b,m);
    vector<pair<int,int>>combined,ppref(n+m+1);
    for(auto &x: a){
        combined.push_back({x,0});
    }
    for(auto &x: b){
        combined.push_back({x,1});
    }
    sort(all(combined),[&](pair<int,int>&a,pair<int,int>&b){
        if(a.first!=b.first)
            return a.first>b.first;
        return a.second<b.second;
    });
    ppref[0] = {0,0};
    total_pref[0] = 0;
    for(int i = 1; i<=n+m; i++){
        auto &[f,s] = ppref[i-1];
        if(combined[i-1].second==0){
            ppref[i] = {f+1,s};
        }else{
            ppref[i] = {f,s+1};
        }
        total_pref[i] = total_pref[i-1] + combined[i-1].first;
    }
    while(q--){
        int x,y,z;
        cin>>x>>y>>z;
        int l = 0, r = z;
        while(l<=r){
            int mid = (l+r)/2;
            if(ppref[mid].first<=x and ppref[mid].second<=y){
                l = mid+1;
            }else{
                r = mid-1;
            }
        }
        int curr_total = total_pref[r];
        int rem = z - (ppref[r].first + ppref[r].second);
        if(rem==0){
            cout<<curr_total<<endl;
        }else{
            if(ppref[r].first==x){
                curr_total+=(prefb[ppref[r].second+rem] - prefb[ppref[r].second]);
            }else{
                curr_total+=(prefa[ppref[r].first+rem] - prefa[ppref[r].first]);
            }
            cout<<curr_total<<endl;
        }
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
        // cout<<"Case "<<z<<": ";
        solve();
    }
}