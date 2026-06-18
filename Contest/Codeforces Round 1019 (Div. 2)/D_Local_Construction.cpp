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


void solve()
{
    int n;
    cin>>n;
    vector<int>ans(n);
    vector<pair<int,int>>v(n);
    for(int i = 0; i<n; i++){
        cin>>v[i].first;
        v[i].second = i;
    }
    int l = 1, r = n, op = 0;
    while(l<r){
        vector<pair<int,int>>tmp;
        if(op){
            int left = 0, p = 0;
            for(auto &[f,s]: v){
                if(f==1){
                    ans[s] = l++;
                }else{
                    tmp.push_back({f-1,s});
                    left++;
                }
                if(f<=-1)
                    break;
                p++;
            }
            for(int i = sz(v)-1; i>p; i--){
                auto &[f,s] = v[i];
                if(f==1){
                    ans[s] = l++;
                }else{
                    tmp.push_back({f-1,s});
                }
            }
            sort(all(tmp),[&](pair<int,int>&a, pair<int,int>&b){
                return a.second<b.second;
            });
        }else{
            int left = 0, p = 0;
            for(auto &[f,s]: v){
                if(f==1){
                    ans[s] = r--;
                }else{
                    tmp.push_back({f-1,s});
                    left++;
                }
                if(f<=-1)
                    break;
                p++;
            }
            for(int i = sz(v)-1; i>p; i--){
                auto &[f,s] = v[i];
                if(f==1){
                    ans[s] = r--;
                }else{
                    tmp.push_back({f-1,s});
                }
            }
            sort(all(tmp),[&](pair<int,int>&a, pair<int,int>&b){
                return a.second<b.second;
            });
        }
        op^=1;
        v = tmp;
    }
    ans[v[0].second] = l;
    for(auto &x: ans)
        cout<<x<<" ";
    cout<<endl;
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