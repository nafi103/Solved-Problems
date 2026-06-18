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
#define inf 1e10+10
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
const pair<int,int> zero = {0,0}, INF = {inf,inf};

int n,q;

pair<int,int> bs(int l, int r, int k, vector<int>&pos, vector<int>&v){
    if(l==r){
        return (pos[k]==l ? zero : INF);
    }
    int mustl = 0, reml = k, remr = n-1-k, mustr = 0;
    while(l<=r){
        if(reml<0 or remr<0){
            return INF;
        }
        int mid = (l+r)/2;
        if(mid==pos[k])
            return {mustl,mustr};
        else if(mid<pos[k]){
            reml--;
            if(v[mid]>k){
                mustl++;
            }
            l = mid+1;
        }
        else{
            remr--;
            if(v[mid]<k){
                mustr++;
            }
            r = mid-1;
        }
    }
    return INF;
}

void solve()
{
    cin>>n>>q;
    vector<int>v(n),pos(n);
    for(int i = 0; i<n; i++){
        cin>>v[i];
        v[i]--;
        pos[v[i]] = i;
    }
    while(q--){
        int l,r,k;
        cin>>l>>r>>k;
        l--,r--,k--;
        auto [needless,needbig] = bs(l,r,k,pos,v);
        if(pos[k]>=l and pos[k]<=r){
            int need = (max(needless,needbig))*2;
            if(need>=n)
                need = -1;
            cout<<need<<" ";
        }else{
            cout<<-1<<" ";
        }
    }
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