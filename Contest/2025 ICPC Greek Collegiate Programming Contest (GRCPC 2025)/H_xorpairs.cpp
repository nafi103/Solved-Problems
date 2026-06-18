#include<bits/stdc++.h>
using namespace std;
 #define int long long
#define endl "\n"
const int mod = 1e9+7;
 vector<int>num;
int len;
int dp[12][2][16];
 void make(int n){
    num.clear();
    while(n>0){
        num.push_back(n%10);
        n/=10;
    }
    reverse(num.begin(),num.end());
}
 int f(int pos, int flag, int Xor){
    if(pos==len)
        return Xor;
    int &ans = dp[pos][flag][Xor];
    if(ans!=-1){
        return ans;
    }
    ans = 0;
    for(int i = (flag==0 ? num[pos]:9); i>=0; i--){
        int new_flag = flag | (i<num[pos]);
        int new_xor = Xor^i;
        ans = (ans + f(pos+1, new_flag, new_xor))%mod;
    }
    return ans;
}
 void solve(){
    int n,del = 0, ans = 0;
    cin>>n;
    vector<int>v(n),d(n);
    for(auto &x: v){
        cin>>x;
    }
    sort(v.begin(),v.end());
    for(int i = 0; i<n; i++){
        if(v[i]==0){
            d[i]=0;
            continue;
        }
        make(v[i]);
        len = num.size();
        for(int i = 0; i<len; i++){
            for(int j= 0; j<2; j++){
                for(int k = 0; k<16; k++){
                    dp[i][j][k] = -1;
                }
            }
        }
        int my_xor = 0;
        for(auto &x: num){
            my_xor = my_xor^x;
        }
        d[i] = f(0,0,0);
        ans = (ans +((d[i]*i)% mod - del + mod)%mod)%mod;
        del =(del + d[i] - my_xor + mod)%mod;
    }
    cout<<ans<<endl;
}
 int32_t main(){
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    int t = 1;
//    cin>>t;
    for(int z = 1; z<=t; z++){
//        cout<<"Case "<<z<<": ";
        solve();
    }
    return 0;
}
 