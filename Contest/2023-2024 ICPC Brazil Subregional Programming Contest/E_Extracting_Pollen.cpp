#include <bits/stdc++.h>
 using namespace std;
 auto dbg(int x) {
 cout << " " << x << endl;
}
 int digit_sum(int n){
 int x = 0;
 while(n>0){
  x+=(n%10);
  n/=10;
 }
 return x;
}
 int32_t main() {
 ios_base::sync_with_stdio(0), cin.tie(0), cout.tie(0);
 int n, k;  
 cin >> n >> k;
 vector<int>cnt(1000010, 0);
 for(int i = 0; i<n; i++){
  int x;
  cin>>x;
  cnt[x]++;
 }
 for(int i = 1000000; i>=0; i--){
  if(cnt[i]<k){
   k-=cnt[i];
   cnt[i-digit_sum(i)]+=cnt[i];
  }else{
   cout<<digit_sum(i)<<endl;
   return 0;
  }
 }
 cout<<0<<endl;
}