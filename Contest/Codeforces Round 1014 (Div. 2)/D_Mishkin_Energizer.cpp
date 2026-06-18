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
    int save = n;
    string str;
    cin>>str;
    map<char,int>mp;
    mp['L'] = 0;
    mp['I'] = 0;
    mp['T'] = 0;
    for(auto &x: str){
        mp[x]++;
    }
    if(mp['L']==mp['T'] and mp['T']==mp['I']){
        cout<<0<<endl;
        return;
    }
    vector<pair<int,char>>have;
    for(auto &[f,s]: mp){
        have.push_back({s,f});
    }
    vector<int>ans;
    sort(all(have));
    for(int i = 0; i<n-1; i++){
        if(str[i]!=str[i+1]){
            set<char>s = {'L','I','T'};
            s.erase(str[i]);
            s.erase(str[i+1]);
            str.insert(str.begin()+i+1,1,*s.begin());
            ans.push_back(i+1);
            n++;
            if(*s.begin()==have[0].ss){
                have[0].ff++;
            }else if(*s.begin()==have[1].ss){
                have[1].ff++;
            }else{
                have[2].ff++;
            }
            break;
        }
        sort(all(have));
    }
    while(have[0].ff<have[2].ff or have[1].ff<have[2].ff){
        bool flag = false;
        for(int i = 0; i<n-1; i++){
            if(have[0].ff<have[2].ff and str[i]!=str[i+1] and str[i]!=have[0].ss and str[i+1]!=have[0].ss){
                str.insert(str.begin()+i+1,1,have[0].ss);
                ans.push_back(i+1);
                n++;
                have[0].ff++;
                flag = true;
                break;
            }else if(have[1].ff<have[2].ff and str[i]!=str[i+1] and str[i]!=have[1].ss and str[i+1]!=have[1].ss){
                str.insert(str.begin()+i+1,1,have[1].ss);
                ans.push_back(i+1);
                n++;
                have[1].ff++;
                flag = true;
                break;
            }
        }
        if(!flag){
            cout<<-1<<endl;
            return;
        }
    }
    if(have[1].ff==have[0].ff and have[0].ff==have[2].ff and sz(ans)<=2*save){
        cout<<sz(ans)<<endl;
        for(auto &x: ans){
            cout<<x<<endl;
        }
    }else{
        cout<<-1<<endl;
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
        // google(z);
        solve();
    }
}