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
#define c first
#define alp second
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
    string str;
    cin>>str;
    vector<int>divisors;
    for(int i = 1; i*i<=n; i++){
        if(n%i==0){
            int another = n/i;
            divisors.pb(i);
            if(another!=i) divisors.pb(another);
        }
    }
    vector<pair<int,char>>cnt(26);
    for(int i = 0; i<26; i++){
        cnt[i] = {0,'a'+i};
    }
    for(int i = 1; i<=n; i++){
        cnt[str[i-1]-'a'].c++;
    }
    sort(cnt.rbegin(),cnt.rend());
    while(cnt.back().c==0){
        cnt.pop_back();
    }
    int use = n, ans = n;
    for(int i = 0; i<sz(divisors); i++){
        int same = 0, have = 0,div = divisors[i];
        if(26*div<n)
            continue;
        for(auto &[x,c]: cnt){
            if(have==n){
                break;
            }
            have+=div;
            same+=min(div,x);
        }
        int not_same = n-same;
        if(not_same<ans){
            use = div;
            ans = not_same;
        }
    }
    int r = n/use;
    vector<int>extra(r);
    vector<int>pos(26,-1);
    for(int i = 0; i<r; i++){
        extra[i] = use-cnt[i].c;
        cnt[i].c = use;
        pos[cnt[i].alp - 'a'] = i;
    }
    r--;
    string t = "";
    for(auto &x: str){
        int curr_pos = pos[x-'a'];
        if(curr_pos==-1 or cnt[curr_pos].c==0){
            t.pb(cnt[r].alp);
            extra[r]--;
            if(extra[r]==0)
                r--;
        }else{
            cnt[curr_pos].c--;
            t.pb(cnt[curr_pos].alp);
        }
    }
    cout<<ans<<endl<<t<<endl;
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