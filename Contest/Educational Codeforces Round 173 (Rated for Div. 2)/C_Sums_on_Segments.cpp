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
    int n;
    cin>>n;
    vector<int>v(n);
    readv(v);
    int not_one = -1, mx_one = 0, mx_mone = 0, one = 0, mone = 0;
    for(int i = 0; i<n; i++){
        if(v[i]==1){
            one++;
            mone--;
        }else if(v[i]==-1){
            mone++;
            one--;
        }else{
            mone = 0;
            one = 0;
            not_one = i;
        }
        if(one<0) one = 0;
        if(mone<0) mone = 0;
        mx_mone = max(mone, mx_mone);
        mx_one = max(one, mx_one);
    }
    mx_mone = max(mx_mone,mone);
    mx_one = max(mx_one,one);
    set<int>ans;
    for(int i = 0; i<=mx_one; i++){
        ans.insert(i);
    }
    for(int i = 1; i<=mx_mone; i++){
        ans.insert(-i);
    }
    if(not_one!=-1){
        int mxol = 0, mxor = 0, mxmol = 0, mxmor = 0;
        one = 0, mone = 0;
        for(int i = not_one-1; i>=0; i--){
            if(v[i]==1){
                one++;
                mone--;
            }else{
                one--;
                mone++;
            }
            mxol = max(one,mxol);
            mxmol = max(mone,mxmol);
        }
        one = 0;
        mone = 0;
        for(int i = not_one+1; i<n; i++){
            if(v[i]==1){
                one++;
                mone--;
            }else{
                one--;
                mone++;
            }
            mxor = max(one,mxor);
            mxmor = max(mone,mxmor);
        }
        one = mxor+mxol;
        mone = mxmor+mxmol;
        for(int i = 0; i<=one; i++){
            ans.insert(v[not_one]+i);
        }
        for(int i = 1; i<=mone; i++){
            ans.insert(v[not_one]-i);
        }
    }
    cout<<sz(ans)<<endl;
    writev(ans);
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